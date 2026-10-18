(** * bifunctors *)

Require Export functor.

Local Open Scope cat_scope.

(*TMP-UNIV: * -> × *)
Definition app11 {A B D: Type} (F: A∧B -> D) (a: ob A) (b: ob B): D := F(a,b).
(*TMP-UNIV: * -> × *)
Definition app22 {A B D: Quiver} (F: PreFunctor (A∧B) D) {a a' b b'}
  (f: A a a') (g: B b b'): app11 F a b ~> app11 F a' b' :=
  @Fhom _ _ F (a,b) (a',b') (f,g).
Instance app22_eqv {A B D F a a' b b'}: Proper (eqv ==> eqv ==> eqv) (@app22 A B D F a a' b b').
Proof. intros ??? ???. exact/extensional. Qed.


