From CRIS.common Require Import CRIS.
From CRIS.cell Require Import CellA CtxHeader CellHeader.

Set Implicit Arguments.

Module MainAS. Section MainAS.
  Import CellA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellGS}.

  Definition main : string := "Main.main".
  
  Definition main_spec : fspec :=
    fspec_simple (fun _ : unit =>
                    ( fun arg => cell 0
                    , fun ret => True))%I.

End MainAS. End MainAS.

Module MainA. Section MainA.
  Import CellA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIO: !cellGS}.
                
  Definition scopes : list string := [].

  Definition start: Any.t -> itree crisE Any.t :=
    λ arg, trigger (Call MainAS.main arg).
  
  Definition main: Any.t -> itree crisE Any.t :=
    λ _,
      '_: unit <- ccallU CtxHdr.foo tt;;
      '_: unit <- trigger (IO "Print" (42%Z));;
      Ret tt↑.
  
  Definition fnsems : fnsemmap :=
    {[entry             # (msk_scp scopes msk_true, (fsp_some MainAS.main_spec, start));
      funid MainAS.main # (msk_scp scopes msk_true, (fsp_some MainAS.main_spec, main))
    ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.

End MainA. End MainA.
