(* tested with Rocq 9.1, HB 1.10.1, mathcomp 2.5, all from opam *)

From HB Require Export structures.
From mathcomp Require Export ssreflect ssrfun ssrbool.
From Stdlib Require Export Setoid Morphisms Basics.

(* standalone structure for setoids *)
HB.mixin Record has_setoid S := { eqv: relation S; Equivalence_eqv: Equivalence eqv }.
HB.structure Definition Setoid := { S of has_setoid S }.
Existing Instance Equivalence_eqv.
Infix "≡" := eqv (at level 80).

HB.mixin Record has_t X := { t: Type }.
HB.structure Definition T := { X of has_t X }.
Arguments t: clear implicits.

HB.mixin Record has_setoid_t X of T X := { t_setoid: Setoid (@t X) }.
HB.structure Definition ST := { X of has_setoid_t X & }.
HB.instance Definition _ (X: ST.type) := Setoid.copy (t X) (Setoid.Pack _ t_setoid).

HB.mixin Record has_f X of T X := { (* l1 *)
    f1: t X -> t X;
    f2: t X -> t X -> t X;
  }.
HB.structure Definition f := { X of has_f X & }. (* l2 *)

HB.mixin Record has_Sf X of f X & ST X := { (* l3 *)
  f1_eqv: Proper (eqv ==> eqv) (@f1 X);
  f2_eqv: Proper (eqv ==> eqv ==> eqv) (@f2 X);
}.
HB.structure Definition Sf := { X of has_Sf X & }. (* l4 *)
Existing Instance f1_eqv.
Existing Instance f2_eqv.

Goal forall X: Sf.type, forall g h: t X, g ≡ h -> f1 g ≡ f1 h.
Proof.
  intros*H. rewrite H. reflexivity.
Qed.

Goal forall X: Sf.type, forall g h: t X, g ≡ h -> f2 g h ≡ f2 h h.
Proof.
  intros*H. Fail rewrite H.     (* should work *)
Abort.

(*

two "fixes":

1. replace T with ST on l1
   -> fixes the rewrite, but not satisfactory for me as it changes the hierarchy

2. make f uppercase on l2, l3 !!
   -> also fixes the rewrite, probably because the mixins are then assembled in a different way on l4 ?

not clear to me whether this is a bug in setoid_rewrite, in hierarchy_builder, or a bad interaction between them ; I find it strange that the problem only arises with binary functions


not clear I'll manage to find the right names to impose a working mixin order in my initial scenario...

 *)
