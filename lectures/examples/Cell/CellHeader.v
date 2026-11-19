From CRIS.common Require Import CRIS.

Module CellHdr.
  Definition mn := "Cell".

  Definition fn (method: string) :=
    mn +:+ "." +:+ method.

  Definition set := fnsig (fn "set") (fntyp Z ()).
  Definition get := fnsig (fn "get") (fntyp () Z).
End CellHdr.

