From CRIS.common Require Import CRIS.

Set Implicit Arguments.
Local Open Scope nat_scope.

(** A sequential memoization example for every natural-number input.
    A sparse memo table grows as results are computed; an absent entry
    represents the -1 sentinel.  Natural numbers avoid integer overflow. *)

Module FibH.

Definition fibonacci := fnsig "Fibonacci.fibonacci" (fntyp nat nat).
Definition scopes := ["Fibonacci"].

End FibH.

Module FibI. Section FibI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** The implementation reads the memo table before branching.  On a
      miss it makes ordinary recursive calls, then reads the current
      table again so that saving this result preserves recursive updates. *)

  Definition memo := "Fibonacci" ↯ "memo".
  
  Definition cache := gmap nat nat.
  
  Definition body (n : nat) : itree crisE nat :=
    'xs : cache <- cgetU memo;;
    match xs !! n with
    | Some v => Ret v
    | None =>
        v <- match n with
             | 0 => Ret 0
             | 1 => Ret 1
             | S (S m) =>
                 a <- ccallU FibH.fibonacci (S m);;
                 b <- ccallU FibH.fibonacci m;;
                 Ret (a + b)
             end;;
        ys <- cgetU memo;;
        cput memo (<[n := v]> (ys : cache));;;
        Ret v
    end.

  Definition fnsems : fnsemmap :=
    {[fid FibH.fibonacci # (msk_scp FibH.scopes msk_true,
      (None, cfunU FibH.fibonacci body))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := FibH.scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[memo # (∅ : cache)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
  
End FibI. End FibI.

Module FibA. Section FibA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' =>
        match n' with
        | 0 => 1
        | S n'' => fib n' + fib n''
        end
    end.
  
  Definition body (n : nat) : itree crisE nat :=
    Ret (fib n).

  Definition fnsems : fnsemmap :=
    {[fid FibH.fibonacci # (msk_scp FibH.scopes msk_true,
      (None, cfunU FibH.fibonacci body))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := FibH.scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
               
End FibA. End FibA.

Module FibCorrect. Section FibCorrect.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition cache_ok (xs : FibI.cache) : Prop :=
    forall n v, xs !! n = Some v -> v = FibA.fib n.

  Lemma cache_ok_initial : cache_ok ∅.
  Proof.
    intros n v Hlookup. rewrite lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma cache_ok_insert xs n :
    cache_ok xs -> cache_ok (<[n := FibA.fib n]> xs).
  Proof.
    intros Hvalues i v Hlookup.
    apply fin_maps.lookup_insert_Some in Hlookup.
    destruct Hlookup as [(-> & <-) | [_ Hlookup]].
    - reflexivity.
    - eapply Hvalues; exact Hlookup.
  Qed.
  
  (** The source has no state.  Every entry in the target memo table
      contains the Fibonacci number at its own index. *)
  Definition Ist (STATE : stateGS Σ) : iProp Σ :=
    (∃ xs : FibI.cache, FibI.memo ↦tgt xs↑ ∗ ⌜cache_ok xs⌝)%I.
  
  Section Correctness.
    Context `{STATE : !stateGS Σ}.
    Context (R_s R_t : Type) (Ep : coPset * coPset).
    Context (g : forall R_s R_t,
      retr_type Σ R_s R_t -> bool -> bool ->
      itree crisE R_s -> itree crisE R_t -> iProp Σ).
    Context (RR : retr_type Σ R_s R_t).

    Local Notation sim :=
      (wsim (sandbox_fnsemmap FibA.t.(Mod.fnsems))
        (sandbox_fnsemmap FibI.t.(Mod.fnsems)) (Ist STATE)
        Ep g R_s R_t RR).

    (** A continuation form of correctness lets induction inline the two
        recursive target calls while the source stays at its return. *)
    Lemma sim_call n :
      forall ps pt (xs : FibI.cache) i_s (k_t : Any.t -> itree crisE R_t),
      cache_ok xs ->
      FibI.memo ↦tgt xs↑ -∗
      (∀ ys : FibI.cache, ⌜cache_ok ys⌝ -∗ FibI.memo ↦tgt ys↑ -∗
        sim ps true i_s (k_t (FibA.fib n)↑)) -∗
      sim ps pt i_s
        (r <- trigger (Call (fn_name FibH.fibonacci) n↑);; k_t r).
    Proof.
      induction n using (well_founded_induction lt_wf).
      intros ps pt xs i_s k_t Hxs.
      iIntros "MEM CONT".
      cInlineT. rewrite /cfunU /FibI.body.
      cStepsT. destruct (xs !! n) as [v|] eqn:Hentry.
      - rewrite (Hxs n v Hentry).
        cStepsT. iApply ("CONT" with "[] MEM"). done.
      - destruct n as [|[|m]]; cStepsT.
        + iApply ("CONT" with "[] MEM").
          iPureIntro. exact (cache_ok_insert 0 Hxs).
        + iApply ("CONT" with "[] MEM").
          iPureIntro. exact (cache_ok_insert 1 Hxs).
        + iApply (H (S m) ltac:(lia) ps true xs i_s _ Hxs with "MEM").
          iIntros (ys) "%Hys MEM". cStepsT.
          iApply (H m ltac:(lia) ps true ys i_s _ Hys with "MEM").
          iIntros (zs) "%Hzs MEM". cStepsT.
          iApply ("CONT" with "[] MEM"). iPureIntro.
          exact (cache_ok_insert (S (S m)) Hzs).
    Qed.
  End Correctness.

  Lemma sim_fibonacci :
    ⊢ ISim.sim_fun open FibA.t FibI.t Ist (fid FibH.fibonacci).
  Proof.
    cStartFunSim. rewrite /FibA.body /FibI.body.
    cStepsS.
    destruct (Any.downcast arg) as [n|] eqn:Harg;
      cStepsS; try contradiction.
    iDestruct "IST" as (xs) "(MEM & %Hxs)".
    cStepsT. rewrite Harg. cStepsT.
    destruct (xs !! n) as [v|] eqn:Hentry.
    - rewrite (Hxs n v Hentry). cStepsT.
      cStep. iSplit; first done. iExists xs. iFrame. done.
    - destruct n as [|[|m]]; cStepsT.
      + cStep. iSplit; first done.
        iExists _. iFrame. iPureIntro.
        exact (cache_ok_insert 0 Hxs).
      + cStep. iSplit; first done.
        iExists _. iFrame. iPureIntro.
        exact (cache_ok_insert 1 Hxs).
      + iApply (sim_call _ _ _ (S m) _ _ _ _ Hxs with "MEM").
        iIntros (ys) "%Hys MEM". cStepsT.
        iApply (sim_call _ _ _ m _ _ _ _ Hys with "MEM").
        iIntros (zs) "%Hzs MEM". cStepsT.
        cStep. iSplit; first done.
        iExists _. iFrame. iPureIntro.
        exact (cache_ok_insert (S (S m)) Hzs).
  Qed.

  Lemma sim : ⊢ ISim.t open FibA.t FibI.t Ist.
  Proof.
    cStartModSim.
    - iPoseProof (state_init_tgt_acc _ _ FibI.memo with "TGT") as
        (ov) "(%Hmemo & MEM & _)".
      { set_solver. }
      simpl_map. subst ov. iExists (∅ : FibI.cache). iFrame. iPureIntro.
      apply cache_ok_initial.
    - iApply sim_fibonacci.
  Qed.

  Theorem refinement : ⊢ ctx_refines FibI.t FibA.t.
  Proof.
    iApply main_adequacy. iApply sim.
  Qed.
End FibCorrect. End FibCorrect.
