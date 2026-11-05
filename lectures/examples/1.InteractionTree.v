Require Import String Program.

Variant SysEvent : Type -> Type :=
| sys_f (arg: nat) : SysEvent string
| sys_g (arg: string) : SysEvent nat
.  

(* SysEvent nat = { sys_g "", sys_g "gil", sys_g "hur", ... } *)
(* SysEvent string = { sys_f 3, sys_f 0, sys_f 7, ... } *)

CoInductive itree (E: Type ->Type) (R: Type): Type :=
| Ret (r: R)
| Tau (t: itree E R)
| Vis {A: Type} (e : E A) (k : A -> itree E R)
.

Arguments Ret {E R}.
Arguments Tau {E R}.
Arguments Vis {E R A}.

(* Keep the continuation outside the cofixpoint so guarded callers can use bind. *)
Definition bind {E: Type->Type} {R0 R: Type}
  (t: itree E R0) (s: R0 -> itree E R) : itree E R :=
  (cofix go (t: itree E R0) : itree E R :=
    match t with
    | Ret r => s r
    | Tau t' => Tau (go t')
    | @Vis _ _ A e k => Vis e (fun a => go (k a))
    end) t.

CoFixpoint translate {E1 E2: Type -> Type} {R}
  (f: forall A, E1 A -> E2 A) (t: itree E1 R) : itree E2 R :=
  match t with
  | Ret r => Ret r
  | Tau t' => Tau (translate f t')
  | Vis e k => Vis (f _ e) (fun a => translate f (k a))
  end.

CoFixpoint interp {E: Type -> Type} {A R: Type}
  (body: A -> itree E (A + R)) (t: itree E (A + R))
  : itree E R
  :=
  match t with
  | Ret (inr r) => Ret r
  | Ret (inl a') => Tau (interp body (body a'))
  | Tau t => Tau (interp body t)
  | Vis e k => Vis e (fun a => interp body (k a))
  end.

(** State Monad **)

Variant StateEvent {K V: Type} : Type -> Type :=
| Put (k: K) (v: V) : StateEvent unit
| Get (k: K) : StateEvent (option V)
.

Definition sumE (E1 E2: Type -> Type) : Type -> Type :=
  fun A => (E1 A + E2 A)%type.

CoFixpoint interp_state {E K V S R}
  (put: K -> V -> S -> itree E (S * unit))
  (get: K -> S -> itree E (S * option V))
  (t: itree (sumE E (@StateEvent K V)) R)
  (s: S)
  : itree E R
  :=
  match t with
  | Ret r => Ret r
  | Tau t' => Tau (interp_state put get t' s)
  | Vis (inl e) c => Vis e (fun a => interp_state put get (c a) s)
  | Vis (inr e) c =>
    match e in StateEvent A return (A -> itree _ R) -> itree E R with
    | Put k v => fun c => bind (put k v s) (fun '(s',_) => Tau (interp_state put get (c tt) s'))
    | Get k => fun c => bind (get k s) (fun '(s',v) => Tau (interp_state put get (c v) s'))
    end c
  end.


  






Definition put {E} (n: nat) : bool -> itree E (bool * unit) :=
  fun st =>
    Ret match n with
    | 0 => (false, tt)
    | _ => (true, tt)
    end.
  
Definition get {E} : bool -> itree E (bool * nat) :=
  fun st =>
    Ret (if st then (st, 1) else (st, 0)).


  

(* key operations: bind, translate, iter, interp, state_monad *)


