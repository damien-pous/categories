(** (co)algebras  *)

Require Export functor.
Require Import arewrite.

Local Open Scope cat_scope.

(** * (co)algebras *)

#[primitive]
HB.mixin Record IsAlgebra {𝐂: Quiver} (F: ob 𝐂 -> ob 𝐂) (A: ob 𝐂) := {
    #[canonical=no] alg: F A ~> A;
  }.
#[short(type="Algebra")]
HB.structure Definition algebra 𝐂 F := { A of IsAlgebra 𝐂 F A }.
Arguments alg {_ _ _}, {_ _}. 

#[primitive]
HB.mixin Record IsCoAlgebra {𝐂: Quiver} (F: ob 𝐂 -> ob 𝐂) (A: ob 𝐂) := {
    #[canonical=no] coalg: A ~> F A;
  }.
#[short(type="CoAlgebra")]
HB.structure Definition coalgebra 𝐂 F := { A of IsCoAlgebra 𝐂 F A }.
Arguments coalg {_ _ _}, {_ _}. 

HB.instance Definition _ {𝐂: Quiver} (F: ob 𝐂 -> ob 𝐂) (A: Algebra F) :=
  IsCoAlgebra.Build (𝐂^op) (funcop F) (obop A) (alg A).
HB.instance Definition _ {𝐂: Quiver} (F: ob 𝐂 -> ob 𝐂) (A: CoAlgebra F) :=
  IsAlgebra.Build (𝐂^op) (funcop F) (obop A) (coalg A).

(* Check fun (C: Quiver) (F: ob C -> ob C) (A: CoAlgebra F) => C^op: Quiver.   *)
(* Check fun (C: Quiver) (F: ob C -> ob C) (A: CoAlgebra F) => funcop F: C^op -> C^op.   *)
(* Check fun (C: Quiver) (F: ob C -> ob C) (A: CoAlgebra F) => obop A: C^op. *)
(* Check fun (C: Quiver) (F: ob C -> ob C) (A: CoAlgebra F) => obop A: Algebra _.   *)
(* Check fun (C: Quiver) (F: ob C -> ob C) (A: Algebra F) => obop A: CoAlgebra _.   *)
(* Check fun (C: PreCat) (F: PreFunctor C C) (A: CoAlgebra F) => obop A: Algebra _.   *)
(* Check fun (C: Cat) (F: Functor C C) (A: CoAlgebra F) => obop A: Algebra _.   *)
(* Check fun (C: Cat) (F: Functor C C) (A: Algebra F) => obop A: CoAlgebra _.   *)


(* TOTHINK: do we really want to infer algebra homomorphisms, or just define them? *)
#[primitive]
HB.mixin Record IsAlgebraHom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F) (f: A ~> B) := {
    #[canonical=no] alg_hom: Fhom F f \; alg B ≡ alg A \; f;
  }.
#[short(type="AlgebraHom")]
HB.structure Definition algebrahom 𝐂 F A B := { f of IsAlgebraHom 𝐂 F A B f }.
Arguments alg_hom {_ _ _ _ _}, {_ _ _ _}. 
Arguments AlgebraHom {_ _}, {_}. 

#[primitive]
HB.mixin Record IsCoAlgebraHom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: CoAlgebra F) (f: A ~> B) := {
    #[canonical=no] coalg_hom: coalg A \; Fhom F f ≡ f \; coalg B;
  }.
#[short(type="CoAlgebraHom")]
HB.structure Definition coalgebrahom 𝐂 F A B := { f of IsCoAlgebraHom 𝐂 F A B f }.
Arguments coalg_hom {_ _ _ _ _}, {_ _ _ _}. 
Arguments CoAlgebraHom {_ _}, {_}. 

HB.instance Definition _ 𝐂 F A B := Setoid.copy (AlgebraHom F A B) (kernel (@algebrahom.sort 𝐂 F A B)).
HB.instance Definition _ (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (Algebra F) AlgebraHom.

HB.instance Definition _ 𝐂 F A B := Setoid.copy (CoAlgebraHom F A B) (kernel (@coalgebrahom.sort 𝐂 F A B)).
HB.instance Definition _ (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (CoAlgebra F) CoAlgebraHom.

(* with the above instances, obop A is seen as an object in the dual of the Coalgebra category *)
(* Fail Check fun (C: Cat) (F: Functor C C) (A: CoAlgebra F) => obop A: Algebra _.   *)
(* Fail Check fun (C: Cat) (F: Functor C C) (A: Algebra F) => obop A: CoAlgebra _.   *)
(* Check fun (C: Cat) (F: Functor C C) (A: CoAlgebra F) => obop A: ob (CoAlgebra F)^op.   *)
(* Check fun (C: Cat) (F: Functor C C) (A: Algebra F) => obop A: ob (Algebra F)^op.   *)
(* Check fun (C: Cat) (F: Functor C C) (A: CoAlgebra F) => obop (A: ob C): Algebra _.   *)
(* Check fun (C: Cat) (F: Functor C C) (A: Algebra F) => obop (A: ob C): CoAlgebra _.   *)

HB.instance Definition _ {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F) (f: AlgebraHom A B) :=
  IsCoAlgebraHom.Build (𝐂^op) (funcop F) _ _ (morphop f) (alg_hom f).
HB.instance Definition _ {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: CoAlgebra F) (f: CoAlgebraHom A B) :=
  IsAlgebraHom.Build (𝐂^op) (funcop F) _ _ (morphop f) (coalg_hom f).

(* Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: A ~> B) => morphop f: _ ~> _. *)
(* Fail Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: A ~> B) => morphop f: CoAlgebraHom _ _. *)
(* Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: AlgebraHom A B) => morphop f: CoAlgebraHom _ _. *)
(* Fail Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: AlgebraHom A B) => morphop f: _ ~>_(CoAlgebra _) _. *)
(* Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: AlgebraHom A B) => (morphop f: CoAlgebraHom _ _): _ ~> _. *)

Lemma alg_hom_idmap (𝐂: Cat) (F: Functor 𝐂 𝐂) (A: Algebra F): Fhom F A \; alg A ≡ alg A \; A. 
Proof. cat. Qed.
HB.instance Definition _ 𝐂 F A := IsAlgebraHom.Build _ _ A A idmap (@alg_hom_idmap 𝐂 F A).

Lemma alg_hom_comp (𝐂: Cat) (F: Functor 𝐂 𝐂) (A B C: Algebra F) (f: A ~> B) (g: B ~> C):
  Fhom F (f \; g) \; alg C ≡ alg A \; (f \; g). 
Proof. rewrite Fcomp. do 2 arewrite alg_hom. cat. Qed.
HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) (A B C: Algebra F) (f: A ~> B) (g: B ~> C) :=
  IsAlgebraHom.Build _ _ A C (f \; g) (@alg_hom_comp 𝐂 F A B C f g).

(* TOTHINK: set arguments so that they always unfold? *)
Definition alg_id {𝐂: Cat} {F: Functor 𝐂 𝐂} (A: Algebra F): A ~> A := idmap: AlgebraHom _ _. 
Definition alg_comp {𝐂: Cat} {F: Functor 𝐂 𝐂} (A B C: Algebra F) (f: A ~> B) (g: B ~> C): A ~> C := f \; g: AlgebraHom _ _. 

HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) := IsPreCat.Build (Algebra F) alg_id alg_comp.

Lemma coalg_hom_idmap (𝐂: Cat) (F: Functor 𝐂 𝐂) (A: CoAlgebra F): coalg A \; Fhom F A ≡ A \; coalg A. 
Proof. exact: (alg_hom_idmap (obop (A: ob 𝐂))). Qed.
HB.instance Definition _ 𝐂 F A := IsCoAlgebraHom.Build _ _ A A idmap (@coalg_hom_idmap 𝐂 F A).

Lemma coalg_hom_comp (𝐂: Cat) (F: Functor 𝐂 𝐂) (A B C: CoAlgebra F) (f: A ~> B) (g: B ~> C):
  coalg A \; Fhom F (f \; g) ≡ (f \; g) \; coalg C. 
Proof. exact: (alg_hom_comp (morphop (coalgebrahom.sort g): AlgebraHom _ _) (morphop (coalgebrahom.sort f): AlgebraHom _ _)). Qed.
HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) (A B C: CoAlgebra F) (f: A ~> B) (g: B ~> C) :=
  IsCoAlgebraHom.Build _ _ A C (f \; g) (@coalg_hom_comp 𝐂 F A B C f g).

(* TOTHINK: set arguments so that they always unfold? *)
Definition coalg_id {𝐂: Cat} {F: Functor 𝐂 𝐂} (A: CoAlgebra F): A ~> A := idmap: CoAlgebraHom _ _. 
Definition coalg_comp {𝐂: Cat} {F: Functor 𝐂 𝐂} (A B C: CoAlgebra F) (f: A ~> B) (g: B ~> C): A ~> C := f \; g: CoAlgebraHom _ _. 

HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) := IsPreCat.Build (CoAlgebra F) coalg_id coalg_comp.

Lemma _coalg_cat (𝐂: Cat) (F: Functor 𝐂 𝐂): IsCat (CoAlgebra F).
Proof.
  split; intros.
  - exact/comp1o. 
  - exact/compo1. 
  - exact/compoA.
  - exact/comp_eqv.
Qed.
HB.instance Definition _ 𝐂 F := @_coalg_cat 𝐂 F.
