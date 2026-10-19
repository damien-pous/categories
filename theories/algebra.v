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

Section s.
Context {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F).
Definition alghom (f: A ~> B) := Fhom F f \; alg B ≡ alg A \; f.
Definition Alghom := sig alghom. 
Coercion Alghom_sort (f: Alghom): A ~> B := sval f.
Definition mk_alghom (f: A ~> B): alghom f -> Alghom := exist _ f. 
Definition algP (f: Alghom): alghom f := proj2_sig f.
End s.
Arguments Alghom {_ _}.
Arguments alghom {_} [_ _ _] _/.
Arguments mk_alghom {_} [_ _ _] &_ _.
HB.instance Definition _ {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (Algebra F) Alghom.

(** ** the category of algebras *)

Section s.
Context {𝐂: Cat} (F: Functor 𝐂 𝐂).

Program Definition Alghom_id (A: Algebra F): A ~> A :=
  mk_alghom idmap _. 
Next Obligation. move=>A/=. cat. Qed.

Program Definition Alghom_comp (A B C: Algebra F) (f: A ~> B) (g: B ~> C): A ~> C :=
  mk_alghom (f \; g) _. 
Next Obligation. move=>A B C f g/=. rewrite Fcomp. do 2 arewrite algP. cat. Qed.

HB.instance Definition _ := IsPreCat.Build (Algebra F) Alghom_id Alghom_comp.

Lemma _alg_cat: IsCat (Algebra F).
Proof.
  split; intros.
  - exact/comp1o. 
  - exact/compo1. 
  - exact/compoA.
  - move=>??????. exact/comp_eqv.
Qed.
HB.instance Definition _ := _alg_cat.

Definition Alghom_self (A: Algebra F): algebra_ (Fhom F (alg A)) ~> A :=
  mk_alghom (alg A) eqv_refl. 

(** ** co Lambek Lemma *)

Section colambek.
  (* TODO: improve insertion of coercions INITIAL.sort and Alghom_sort *)
  Variable A: Initial (Algebra F).
  Abbreviation A' := (INITIAL.sort A). 
  Let FA: Algebra F := algebra_ (Fhom F (alg A')).
  Let b: A' ~> FA := init A FA.
  (*
FA -Fb-> FFA -Fa-> FA
|a       |Fa       |a
V        V         V
A --b--> FA --a--> A
   *)
  Let ba: Alghom_sort b \; alg A' ≡ idmap.
  Proof. exact: (initU (b \; Alghom_self A') (Alghom_id _)). Qed.
  Let ab: alg A' \; Alghom_sort b  ≡ idmap.
  Proof. rewrite -algP-Fcomp ba. cat. Qed.
  HB.instance Definition _ := @IsIso.Build _ _ _ (alg A') (Alghom_sort b) ba ab. 
End colambek.
Check fun A: Initial (Algebra F) => alg (INITIAL.sort A): Iso _ _. 

End s.


