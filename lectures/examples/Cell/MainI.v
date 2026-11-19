From CRIS.common Require Import CRIS.
From CRIS.cell Require Import CellHeader CellA MainA CtxHeader.

Set Implicit Arguments.

Module MainI. Section MainI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition start: Any.t -> itree crisE Any.t :=
    λ arg, trigger (Call MainAS.main arg).

  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      ccallU CellHdr.set (42%Z);;;
      ccallU CtxHdr.foo tt;;;
      x <- ccallU CellHdr.get tt;;
      trigger (@IO Z unit "Print" x);;;
      Ret tt↑.
  
  Definition fnsems : fnsemmap :=
    {[entry             # (msk_real (msk_scp scopes msk_true), (fsp_none, start));
      funid MainAS.main # (msk_real (msk_scp scopes msk_true), (fsp_none, main))
    ]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End MainI. End MainI.
