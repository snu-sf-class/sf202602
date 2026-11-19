From CRIS.common Require Import CRIS.
From CRIS.cell Require Import CellHeader CellA MainA MainI CtxHeader.

Set Implicit Arguments.

Module MainIA. Section MainIA.
  Import CellA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellGS}.

  Context (sp: specmap).
  Context (sp_start: sp.1 !! (funid MainAS.main) = Some (MainAS.main_spec: fspec_rel)).
  Context (sp_foo: sp.1 !! (fid CtxHdr.foo) = None).

  Local Definition CellA := (CellA.t).
  Local Definition MainA := (MainA.t sp).
  Local Definition IstFull (_ : stateGS Σ) : iProp Σ := True%I.

  Lemma simF_start :
    ⊢ ISim.sim_fun open MainA (MainI.t ★ CellA) IstFull entry.
  Proof using sp_start.
    cStartFunSim. unfold MainI.start, MainA.start.
    cStepsS. rewrite sp_start. cStepsS. cForceS _q. cStepsS. cForceS arg. cStepsS.
    cForceS. iFrame. cStepsS. cStepsT. cCall "IST" as (?) "IST".
    cStepsS. cForcesS. iSplit; et. cStepsT. cStep. iSplit; et.
  Qed.
  
  Lemma simF_main :
    ⊢ ISim.sim_fun open MainA (MainI.t ★ CellA) IstFull
        (funid MainAS.main).
  Proof using sp_foo.
    cStartFunSim. unfold MainI.main, MainA.main.

    (* Take cell(0) *)
    cStepsS. iDestruct "ASM" as "[-> CELL]".

    cStepsT. cInlineT.
    (* Give cell(0) *)
    cStepsT. cForcesT. iSplitL "CELL"; et.

    cStepsT.

    (* Take cell(i) *)
    cStepsT. iRename "GRT" into "CELL".

    (* Call Foo.foo() simultaneously *)
    cStepsT. cStepsS. rewrite sp_foo.
    cCall "IST" as (r1) "IST".
    destruct Any.downcast; [|cStepsS; ss].
    cStepsT. cInlineT.
    (* Give cell(i) *)
    cStepsT. cForcesT. iSplitL "CELL"; eauto.

    (* Take cell(i) *)
    cStepsT. iRename "GRT" into "CELL".

    (* Call Print(i) simultaneously *)
    cStepsT. cStepsS. cStep.

    cForcesS. iSplit; et.
    cStep. iFrame. ss.

    Unshelve. all:(exact ()).
  (*SLOW*)Qed.

  Lemma sim : ⊢ ISim.t open MainA (MainI.t ★ CellA) IstFull.
  Proof using sp_start sp_foo.
    cStartModSim.
    - done.
    - iApply simF_start; eauto.
    - iApply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
