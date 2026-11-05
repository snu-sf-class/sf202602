From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.

Module MemSig.
  Definition alloc := fnsig "MemAtom.alloc" (mk_fntyp_t nat val).
  Definition free  := fnsig "MemAtom.free" (mk_fntyp_t val unit).
  Definition load  := fnsig "MemAtom.load" (mk_fntyp_t val Z).
  Definition store := fnsig "MemAtom.store" (mk_fntyp_t (val * Z) unit).
End MemSig.

Module CellSig.
  Definition mn := "Cell".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition set := fnsig (fn "set") (fntyp Z ()).
  Definition get := fnsig (fn "get") (fntyp () Z).
End CellSig.

Section test.
  Context `{!crisG Γ Σ α β τ _S _I}.

(*

 int main(int x) {
   int y = x + 42;
   int* p = malloc(4);
   *p = y;
   foo(p);
   int r = *p;
   return r;
 }

 *)


Definition main (x: Z) : itree crisE Z :=
  y <- Ret (x + 42)%Z;;
  p <- ccallU MemSig.alloc 4;;
  ccallU MemSig.store (p,y);;;
  ccallU (fnsig "foo" (mk_fntyp_t val unit)) p;;;
  r <- ccallU MemSig.load p;;
  Ret r.

Definition sqrt (x: nat) : itree crisE nat :=
  'r: nat <- trigger (Choose nat);;
   trigger (Guarantee (⌜(r * r)%nat = x⌝));;;
   Ret r.

(*
int sum(n: int) {
  int s = 0;
  while (n > 0) {
    s = s + n;        
    n = n - 1;
  }
  return s;
}
*)

Definition sum (n: Z) : itree crisE Z :=
  s <- ITree.iter
  (λ sn,
     if sn.2 >? 0 then      
       s' <- Ret (sn.1 + sn.2)%Z;;
       n' <- Ret (sn.2 - 1)%Z;;
       Ret (inl (s',n'))
     else
       Ret (inr sn.1)
  ) (0,n)%Z;;
  Ret s.

(* Print itree. *)
(* Print itree'. *)
(* Notation itree' E R := (itreeF E R (itree E R)). *)

(* Print itreeF.                          *)

(* CoInductive itree (E : iEvent) (R : Type) : Type := *)
(*   go : itree' E R → itree E R. *)

(* function f () = f (). *)
End test.

(*
Module Cell.
private cv = 0;
def set(v) ≡
  cv := v;
def get() ≡
  ret cv;
End Cell.
*)

Module CellI. Section CellI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CellSig.mn].
  Definition v_cv := (CellSig.mn) ↯ "cv".

  Definition set: Z -> itree crisE () :=
    λ i,
      cput v_cv i;;;
      Ret tt.

  Definition get: () -> itree crisE Z :=
    λ _,
      i <- cgetU v_cv;;
      Ret i.

  Definition fnsems : fnsemmap :=
    {[fid CellSig.set # (msk_real (msk_scp scopes msk_true), (fsp_none, cfunU CellSig.set set));
      fid CellSig.get # (msk_real (msk_scp scopes msk_true), (fsp_none, cfunU CellSig.get get))]}.

  Program Definition smod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_cv # (0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CellI. End CellI.
