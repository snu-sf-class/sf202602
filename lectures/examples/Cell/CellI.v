From CRIS.common Require Import CRIS.
From CRIS.cell Require Import CellHeader CtxHeader.

Module CellI. Section CellI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CellHdr.mn].
  Definition v_cv := (CellHdr.mn) ↯ "cv".

  Definition set: Z -> itree crisE () :=
    λ v,
      cput v_cv v;;;
      Ret tt.

  Definition get: () -> itree crisE Z :=
    λ _,
      i <- cgetU v_cv;;
      Ret i.

  Definition fnsems : fnsemmap :=
    {[fid CellHdr.set # (msk_real (msk_scp scopes msk_true), (fsp_none, cfunU CellHdr.set set));
      fid CellHdr.get # (msk_real (msk_scp scopes msk_true), (fsp_none, cfunU CellHdr.get get))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_cv # (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CellI. End CellI.
