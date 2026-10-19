(** * algebras *)

Require Export functor.
Require Import arewrite.

Local Open Scope cat_scope.

(** ** algebras *)

#[primitive]
HB.mixin Record IsAlgebra {𝐂: BareQuiver} (F: ob 𝐂 -> ob 𝐂) (A: ob 𝐂) := {
    #[canonical=no] alg: F A ~> A;
  }.
#[short(type="Algebra")]
HB.structure Definition ALGEBRA 𝐂 F := { A of IsAlgebra 𝐂 F A }.
Arguments alg {_ _ _}, {_ _}.
Section s.
Context {𝐂: BareQuiver} (F: ob 𝐂 -> ob 𝐂) (A: ob 𝐂).
Definition algebra (a: F A ~> A) := A.
HB.instance Definition _ a := @IsAlgebra.Build 𝐂 F (algebra a) a.
Definition algebra_ a: Algebra F := algebra a.
End s.

(** ** algebras morphisms *)

Definition is_alghom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F) (f: A ~> B) :=
  Fhom F f \; alg B ≡ alg A \; f.
Arguments is_alghom {_} [_ _ _] _/.
#[primitive]
HB.mixin Record IsAlghom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F) (f: A ~> B) := {
    #[canonical=no] alghomP: is_alghom f;
  }.
#[short(type="Alghom")]
HB.structure Definition ALGHOM 𝐂 F A B := { f of IsAlghom 𝐂 F A B f }.
Arguments Alghom {_ _}.
HB.instance Definition _ 𝐂 F A B := Setoid.copy (Alghom A B) (kernel (@ALGHOM.sort 𝐂 F A B)).
Section s.
Context {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F).
Definition alghom (f: A ~> B) (H: is_alghom f) := f.  
HB.instance Definition _ f H := IsAlghom.Build 𝐂 F A B (@alghom f H) H.
Definition alghom_ (f: A ~> B) (H: is_alghom f): Alghom A B := alghom H.  
End s.
Arguments alghom {_} [_ _ _] _ _.
Arguments alghom_ {_} [_ _ _] _ _.

(** ** the category of algebras *)

HB.instance Definition _ {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (Algebra F) Alghom.

Section s.
Context {𝐂: Cat} (F: Functor 𝐂 𝐂).
Implicit Types A B C: Algebra F.   

Lemma alghom_id A: is_alghom A.
Proof. cbn. cat. Qed.
HB.instance Definition _ A := IsAlghom.Build 𝐂 F A A A (alghom_id A).
Definition Alghom_id {A}: Alghom A A := A. 

Lemma alghom_comp A B C (f: Alghom A B) (g: Alghom B C): is_alghom (f \; g).
Proof. cbn. rewrite Fcomp. do 2 arewrite alghomP. cat. Qed.
HB.instance Definition _ A B C (f g: Alghom _ _) := IsAlghom.Build 𝐂 F A C (f \; g) (@alghom_comp A B C f g).
Definition Alghom_comp {A B C} (f g: Alghom _ _): Alghom A C := @comp _ A B C f g. 

HB.instance Definition _ := IsPreCat.Build (Algebra F) (@Alghom_id) (@Alghom_comp).

Lemma _alg_cat: IsCat (Algebra F).
Proof.
  split; intros.
  - exact/comp1o. 
  - exact/compo1. 
  - exact/compoA.
  - move=>??????. exact/comp_eqv.
Qed.
HB.instance Definition _ := _alg_cat.

Definition algnext A := F A.
HB.instance Definition _ A := IsAlgebra.Build 𝐂 F (algnext A) (Fhom F (alg A)).
Definition algnexthom A: algnext A ~>_𝐂 A := alg A.
HB.instance Definition _ A := IsAlghom.Build 𝐂 F (algnext A) A (algnexthom A) eqv_refl.
Definition algnexthom_ A: Alghom (algnext A) A := algnexthom A.

(** ** co Lambek Lemma *)

Section colambek.
  (* TODO: improve insertion of coercions INITIAL.sort and Alghom_sort *)
  Variable A: Initial (Algebra F).
  Abbreviation A' := (INITIAL.sort A). 
  Abbreviation FA := (algnext A': Algebra F). 
  Let b: A' ~> FA := init A FA.
  (*
FA -Fb-> FFA -Fa-> FA
|a       |Fa       |a
V        V         V
A --b--> FA --a--> A
   *)
  Let ba: ALGHOM.sort b \; alg A' ≡ idmap.
  Proof. exact: (initU (b \; algnexthom_ A') idmap). Qed.
  Let ab: alg A' \; b  ≡ idmap.
  Proof. rewrite -alghomP-Fcomp ba. cat. Qed.
  HB.instance Definition _ := @IsIso.Build _ _ _ (alg A') b ba ab. 
End colambek.
Check fun A: Initial (Algebra F) => alg (INITIAL.sort A): Iso _ _. 

End s.


