From HB Require Export structures.
Set Implicit Arguments.

Module U.
Set Universe Polymorphism.
Definition ob (C: Type) := C. 
Fail HB.mixin Record IsQuiver (C: Type) := { hom: ob C -> ob C -> Type }. 
End U.

Definition ob (C: Type) := C.
HB.mixin Record IsQuiver (C: Type) :=
  { hom: ob C -> ob C -> Type }.
HB.structure Definition quiver :=
  {C of IsQuiver C}.
Coercion hom: quiver.type >-> Funclass. 

HB.mixin Record IsQuiverMorphism (C D: quiver.type) (F: ob C -> ob D) :=
  { Fhom: forall A B, C A B -> D (F A) (F B) }.
HB.structure Definition quivermorphism C D :=
  {F of IsQuiverMorphism C D F}.

Unset Universe Checking.
HB.instance Definition _ := IsQuiver.Build quiver.type quivermorphism.type. 
