(* concrete (bare) quivers for defining diagrams for (co)limits *)

Require Import cat.
Open Scope cat_scope.

Definition discrete (T: Type) := T.
HB.instance Definition _ T := IsBareQuiver.Build (discrete T) (fun _ _ => False). 

Variant span := L | C | R.
Variant spanhom: span -> span -> Set :=
  | cl: spanhom C L
  | cr: spanhom C R.
HB.instance Definition _ := IsBareQuiver.Build span spanhom.

Definition cospan := span^op.
HB.instance Definition _ := BAREQUIVER.on cospan.

Variant two := S | T.
Variant twohom: two -> two -> Set :=
  | st1: twohom S T
  | st2: twohom S T.
HB.instance Definition _ := IsBareQuiver.Build two twohom.

Definition omega := nat.
Variant omegahom: omega -> omega -> Set :=
  | next: forall n, omegahom n (Datatypes.S n).
HB.instance Definition _ := IsBareQuiver.Build omega omegahom.
