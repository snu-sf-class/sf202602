From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.filter Require Import FilterComm.
From CRIS.proofmode Require Import BiEnrichedProset.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.cell Require Import CellHeader CellA CellI MainA MainI
  CellProof MainProof CtxHeader.

Section CellAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _CELL: !cellGS}.

  Variable Ctx : SMod.t.
  Hypothesis ctx_real: SMod.is_real Ctx.
  Hypothesis ctx_mod_wf: Mod.wf (SMod.to_mod ∅ Ctx).
  Hypothesis ctx_cancellable : SMod.cancellable Ctx.
  Hypothesis ctx_has_input: fid CtxHdr.input ∈ dom (SMod.fnsems Ctx).
  Hypothesis ctx_has_foo: fid CtxHdr.foo ∈ dom (SMod.fnsems Ctx).
  Hypothesis ctx_main_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems MainI.t) → False.
  Hypothesis ctx_cell_disj:
    ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems CellI.t) → False.
  Hypothesis ctx_main_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes MainI.t) → False.
  Hypothesis ctx_cell_scope_disj:
    ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes CellI.t) → False.

  Local Definition Ctx_filtered : SMod.t := SMod.filter (CFilter.msk_filter_out {[MainAS.main]}) (SMod.filter SFilter.msk_filter_out Ctx).
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel (MainA.smod ☆ Ctx_filtered)).
  Local Definition mod_tgt : Mod.t := MainI.t ★ CellI.t ★ SMod.to_mod ∅ Ctx.

  Local Definition sp : specmap := SMod.sp_from (MainA.smod ☆ Ctx_filtered).
  Local Definition mod_src : Mod.t := SMod.to_mod sp MainA.smod ★ SMod.to_mod ∅ Ctx.

  Local Definition init_cond : iProp Σ :=
    (CellA.init_cond)%I.

  Lemma sp_input: sp.1 !! fid CtxHdr.input = None.
  Proof.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with.
    assert (FIND: exists x, SMod.fnsems Ctx !! fid CtxHdr.input = Some (Some x)).
    { eapply elem_of_dom in ctx_has_input. inv ctx_has_input. eauto.
      inv ctx_mod_wf. destruct x; eauto.
      destruct (SMod.fnsems Ctx !! fid CtxHdr.input) eqn:FIND; ss.
      inv H. hexploit (wf_fns (fid CtxHdr.input)).
      { rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND //. }
      i. ss. inv H.
    }
    des. rewrite !lookup_fmap FIND. ss. destruct x, p. eauto.
  (*SLOW*)Qed.

  Lemma sp_foo: sp.1 !! fid CtxHdr.foo = None.
  Proof.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with.
    assert (FIND: exists x, SMod.fnsems Ctx !! fid CtxHdr.foo = Some (Some x)).
    { eapply elem_of_dom in ctx_has_foo. inv ctx_has_foo. eauto.
      inv ctx_mod_wf. destruct x; eauto.
      destruct (SMod.fnsems Ctx !! fid CtxHdr.foo) eqn:FIND; ss.
      inv H. hexploit (wf_fns (fid CtxHdr.foo)).
      { rewrite /Mod.fnsems /SMod.to_mod lookup_fmap FIND //. }
      i. ss. inv H.
    }
    des. rewrite !lookup_fmap FIND. ss. destruct x, p. et.
  (*SLOW*)Qed.

  Lemma sp_main: sp.1 !! funid MainAS.main = Some (MainAS.main_spec: fspec_rel).
  Proof.
    rewrite lookup_omap !lookup_fmap lookup_omap lookup_union_with. simpl_map.
    destruct (SMod.fnsems Ctx_filtered !! funid MainAS.main) eqn: Lctxf_main; et.
    exfalso. eapply (ctx_main_disj (funid MainAS.main)); rewrite elem_of_dom; et.
    rewrite !lookup_fmap in Lctxf_main.
    destruct (SMod.fnsems _ !! _) eqn: Lctx_main; ss.
  Qed.
  
  (* Apply cancellation to linked spec module *)
  Lemma cancel_src:
    CellA.cell 0 ∗ Cancel.init_res ⊢
      refines mod_src mod_top.
  Proof.
    iIntros "[Hcell Hinit]".
    iApply (refines_trans mod_src
      (SMod.to_mod_cancel sp MainA.smod ★
        SMod.to_mod_cancel sp Ctx_filtered) mod_top).
    iSplitR "Hcell Hinit".
    {
      iApply ctxr_refines.
      rewrite /mod_src.
      jIntros (ctx_refines_BiProset) "(MAIN & CTX)".
      jPoseProof SFilter.smod_filter_intro with "CTX" as "CTX".
      jPoseProof (CFilter.smod_filter_intro {[MainAS.main]})
        with "CTX" as "CTX".

      jPoseProof (Cancel.prepare sp sp MainA.smod)
        with "MAIN" as "MAIN".
      { et; clarify. }
      { et. }
      { et; clarify. }

      jPoseProof (Cancel.prepare ∅ sp Ctx_filtered)
        with "CTX" as "CTX".
      {
        i.
        ltac2:(renames H into Lfn, Lsp).
        eapply CFilter.filter_masked; et.
        rewrite lookup_empty in Lsp.
        apply not_eq_sym, not_eq_None_Some in Lsp.
        destruct Lsp as [? Lsp].
        eapply SMod.sp_core_from_add_lookup in Lsp.
        destruct Lsp as [Lsp|Lsp]; des; cycle 1.
        - eapply SMod.sp_core_from_lookup in Lsp0; des.
          rewrite !lookup_fmap in Lsp0.
          destruct (SMod.fnsems Ctx !! _)
            as [[[? []]|]|] eqn:Lctx_fc; ss; subst.
          eapply ctx_real in Lctx_fc; subst; ss.
        - eapply SMod.sp_core_from_lookup in Lsp; des.
          rewrite lookup_insert_Some in Lsp; des; ss.
          rewrite lookup_singleton_Some in Lsp1. set_solver.
      }
      { et. }
      {
        i.
        rewrite /Ctx_filtered cfilter_comm in H0.
        eapply SFilter.filter_masked; et.
      }
      jFrame.
    }

    rewrite -SMod.to_mod_cancel_add.
    iApply Cancel.cancel.
    { apply SMod.cancellable_add.
      - r; rewrite /= /MainA.fnsems //; mod_tac.
      - eapply CFilter.filter_cancellable, SFilter.filter_cancellable. et.
    }
    { assert (Ce : SMod.fnsems Ctx !! entry = None).
      { eapply not_elem_of_dom. ii. eapply ctx_main_disj; eauto.
        rewrite /MainI.t /MainI.smod /SMod.to_mod /= /Mod.fnsems. set_solver.
      }
      assert (Ht : (SMod.sp_from (MainA.smod ☆ Ctx_filtered)).1 !! entry =
        fsp_some MainAS.main_spec).
      { rewrite /SMod.sp_from /SMod.sp_core_from.
        rewrite !lookup_omap !lookup_fmap lookup_omap lookup_union_with.
        simpl_map; ss. rewrite !lookup_fmap Ce //.
      }
      rewrite Ht; clear Ht. ss; exists tt; split; refl.
    }
    { unfoldPrePost. iIntros (??) "[$ _]". }
    iDestruct "Hinit" as "(X & Y & Z & $ & $)".
    unfoldPrePost. iSplit; et.
  (*SLOW*)Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "Hinit".
    iApply ctxr_refines.
    rewrite /init_cond /mod_src /mod_tgt.

    jIntros (ctx_refines_BiProset) "(MAIN & CELLIO & CTX)".

    jPoseProof main_adequacy with "[Hinit]" "[CELLIO]" as "CELLIO".
    { iApply CellIA.sim. iFrame. }
    { jFrame. }

    jPoseProof main_adequacy with "[MAIN CELLIO]" as "MAIN".
    { iApply MainIA.sim; eauto using sp_input, sp_foo, sp_main. }
    { jFrame. }

    jFrame.
  (*SLOW*)Qed.

  Lemma top_tgt :
    init_cond ∗ CellA.cell 0 ∗ Cancel.init_res ⊢
      refines mod_tgt mod_top.
  Proof.
    iIntros "(Hinit & Hcell & Hcancel)".
    iApply refines_trans. iSplitL "Hinit".
    { iApply src_tgt. iFrame. }
    iApply cancel_src. iFrame.
  Qed.

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt. rewrite !assoc comm.
    eapply Mod.add_wf; cycle 2; et.
    { mod_tac. }
    { eapply NoDup_app. esplits.
      - apply ctx_mod_wf.
      - mod_tac.
      - prove_nodup.
    }
    econs.
    - mod_tac.
    - prove_nodup.
  (*SLOW*)Qed.
End CellAux.

Module CellAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; cellΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; stateΣ].

  Lemma behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : cellGS),
    ∀ (Ctx : SMod.t)
      (ctx_real: SMod.is_real Ctx)
      (ctx_mod_wf: Mod.wf (SMod.to_mod ∅ Ctx))
      (ctx_cancellable : SMod.cancellable Ctx)
      (ctx_has_input: fid CtxHdr.input ∈ dom (SMod.fnsems Ctx))
      (ctx_has_foo: fid CtxHdr.foo ∈ dom (SMod.fnsems Ctx))
      (ctx_main_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems MainI.t) → False)
      (ctx_cell_disj:
        ∀ fno, fno ∈ dom (SMod.fnsems Ctx) → fno ∈ dom (Mod.fnsems CellI.t) → False)
      (ctx_main_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes MainI.t) → False)
      (ctx_cell_scope_disj:
        ∀ mn, mn ∈ (SMod.scopes Ctx) → mn ∈ (Mod.scopes CellI.t) → False),
    ∃ src_res tgt_res,
    refines_lmod
      (Mod.to_lmod (mod_tgt Ctx) tgt_res)
      (Mod.to_lmod (mod_top Ctx) src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV Hinit])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINVempty]".
    iMod cell_alloc as "(% & Hauth & Hcell)".
    iExists _, _, _, _, _.
    iModIntro.
    iIntros (Ctx ctx_real ctx_mod_wf ctx_cancellable ctx_has_input ctx_has_foo
      ctx_main_disj ctx_cell_disj ctx_main_scope_disj ctx_cell_scope_disj).
    iPoseProof (top_tgt Ctx with "[WINV Hinit Hauth Hcell]") as "REF".
    all: try eassumption.
    { rewrite /init_cond /Cancel.init_res.
      iDestruct "Hinit" as "(H0 & H1 & H2 & H3)". iFrame.
    }
    iAssert (⌜∃ src_res, ✓ src_res /\ refines_lmod
      (Mod.to_lmod (mod_tgt Ctx) ε)
      (Mod.to_lmod (mod_top Ctx) src_res)⌝)%I
      with "[WINVempty REF]" as "%Href".
    { iApply refines_adequacy. { eapply tgt_wf; eassumption. } iFrame. }
    destruct Href as [src_res [_ Href]].
    iPureIntro. exists src_res, ε. exact Href.
  (*SLOW*)Qed.
End CellAll.

(* Print Assumptions CellAll.behavioral_refinement. *)
