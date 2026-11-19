From CRIS.common Require Import CRIS.
From CRIS.cell Require Import CellHeader CtxHeader.

Set Implicit Arguments.

Local Definition RA : ucmra :=
  authUR (optionUR (exclR ZO)).
Class cellGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cell_inG :: inG RA Γ;
}.
Class cellGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cellGS_cellGpreS :: cellGpreS;
  cell_name : gname;
}.
Definition cellΓ : HRA := #[RA].
Global Instance subG_cellG `{!crisG Γ Σ α β τ _S _I} :
  subG cellΓ Γ → cellGpreS.
Proof. solve_inG. Defined.

Local Existing Instances cellGS_cellGpreS cell_inG.

Module CellA. Section CellA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_CELLIO: !cellGS}.

  Definition auth (v : Z) : iProp Σ :=
    own cell_name (●E v).

  Definition cell (v : Z) : iProp Σ :=
    own cell_name (◯E v).

  Lemma cell_auth_get v v':
    (* cell v -∗ auth v' -∗ ⌜v = v'⌝. *)
    ⊢ cell v -∗ auth v' -∗ ⌜v = v'⌝.
  Proof.
    rewrite /cell /auth.
    iIntros "P P'"; iCombine "P P'" as "P" gives %wf.
    by apply excl_auth_agree in wf.
  Qed.

  Lemma cell_auth_set v v':
    (* cell v -∗ auth v ==∗ cell v' ∗ auth v'. *)
    ⊢ cell v -∗ auth v -∗ |==> cell v' ∗ auth v'.
  Proof.
    rewrite /cell /auth.
    iIntros "C AU". iCombine "C AU" as "H".
    iMod (own_update with "H") as "[C AU]"; last by (iModIntro; iSplitL "AU"). 
    rewrite comm; apply excl_auth_update.
  Qed.

  Definition set: Z -> itree crisE () :=
    λ v,
      x <- trigger (Take Z);;
      trigger (Assume (CellA.cell x));;;
      trigger (Guarantee (CellA.cell v));;;
      Ret tt.
  
  Definition get: () -> itree crisE Z :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellA.cell x));;;
      trigger (Guarantee (CellA.cell x));;;
      Ret x.

  Definition scopes := [CellHdr.mn].

  Definition fnsems : fnsemmap :=
    {[fid CellHdr.set # (msk_scp scopes msk_true, (None, cfunU CellHdr.set set));
      fid CellHdr.get # (msk_scp scopes msk_true, (None, cfunU CellHdr.get get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ :=
    CellA.auth 0.

  (* We can use ∅ because Cell will be removed before cancellation *)
  Definition t := SMod.to_mod ∅ smod.
End CellA. End CellA.

Lemma cell_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !cellGpreS} :
  ⊢ o=> ∃ (_ : cellGS), CellA.init_cond ∗ CellA.cell 0.
Proof.
  iMod (own_alloc (●E 0%Z ⋅ ◯E 0%Z)) as "[%γt T]".
  { apply auth_both_valid_discrete; esplits; ss. }
  pose (Build_cellGS _ γt) as Hcell.
  rewrite own_op; iExists Hcell. iDestruct "T" as "[T0 T1]"; iFrame.
  done.
Qed.
