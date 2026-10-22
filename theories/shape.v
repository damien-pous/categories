(* concrete (bare) quivers for defining diagrams for (co)limits *)

Require Import cat.
Open Scope cat_scope.

Module Import shape.
Definition discrete (T: Type) := T.

Variant span := L | C | R.
Variant spanhom: span -> span -> Set :=
  | cl: spanhom C L
  | cr: spanhom C R.

Definition cospan := span^op.

Variant two := S | T.
Variant twohom: two -> two -> Set :=
  | st1: twohom S T
  | st2: twohom S T.

Definition omega := nat.
Variant omegahom: omega -> omega -> Set :=
  | next: forall n, omegahom n (Datatypes.S n).
End shape.

HB.instance Definition _ T := IsBareQuiver.Build (discrete T) (fun _ _ => False). 
HB.instance Definition _ := IsBareQuiver.Build span spanhom.
HB.instance Definition _ := BAREQUIVER.on cospan.
HB.instance Definition _ := IsBareQuiver.Build two twohom.
HB.instance Definition _ := IsBareQuiver.Build omega omegahom.
