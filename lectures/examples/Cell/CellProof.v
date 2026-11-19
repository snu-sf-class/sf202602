From CRIS.common Require Import CRIS.
From CRIS.cell Require Import CellHeader CellA CellI CtxHeader.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellIA. Section CellIA.
  Import CellA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellGS}.

  Definition Ist (STATE : stateGS Σ) : iProp Σ :=
    (∃ v, CellI.v_cv ↦tgt v↑ ∗ auth v)%I.

  Local Definition CellI := (CellI.t).
  Local Definition CellA := (CellA.t).

  Lemma simF_set :
    ⊢ ISim.sim_fun open CellA CellI Ist (fid CellHdr.set).
  Proof using.
    cStartFunSim. unfold CellI.set, CellA.set.

    (* Take (x:Z) & cell(x) *)
    cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs.
    rename _q into v. iRename "ASM" into "CELL".

    cStepsT. cStepsS.

    (* Give cell(i) *)
    iDestruct "IST" as (v') "(CV & AUTH)".

    iPoseProof (cell_auth_get with "CELL AUTH") as "<-".
    iMod (cell_auth_set with "CELL AUTH") as "(CELL & AUTH)".

    cStepsT. cForcesS. iSplitL "CELL"; eauto.

    cStep.
    iSplit; first done.
    iExists _. iFrame.
  (*SLOW*)Qed.
  
  Lemma simF_get :
    ⊢ ISim.sim_fun open CellA CellI Ist (fid CellHdr.get).
  Proof using.
    cStartFunSim. unfold CellI.get, CellA.get.

    (* Take (x:Z) & cell(x) *)
    cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs.
    rename _q into v. iRename "ASM" into "CELL".
    iDestruct "IST" as (v') "(CV & AUTH)".

    iPoseProof (cell_auth_get with "CELL AUTH") as "<-".

    cStepsT.

    (* Give cell(x) *)
    cForcesS. iSplitL "CELL"; eauto.
    
    cStep. iSplit; first done.
    iExists _. iFrame.
  (*SLOW*)Qed.
  
  Lemma sim : CellA.init_cond ⊢ ISim.t open CellA CellI Ist.
  Proof using.
    cStartModSim.
    - iPoseProof (state_init_tgt_acc _ _ CellI.v_cv with "TGT") as
        (ov) "(%Hcv & CV & _)".
      { set_solver. }
      simpl_map. subst ov. iExists 0%Z. iFrame.
    - iApply simF_set.
    - iApply simF_get.
  Qed.
End CellIA. End CellIA.
