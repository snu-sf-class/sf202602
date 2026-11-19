From CRIS.common Require Import CRIS.

Module CtxHdr.

  Definition foo := fnsig "foo" (fntyp () ()).
  Definition input := fnsig "input" (fntyp () Z).

End CtxHdr.
