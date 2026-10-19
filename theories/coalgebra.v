(** * coalgebras *)

Require Export algebra.
Require Import arewrite.

Local Open Scope cat_scope.

(** ** coalgebras *)

#[primitive]
HB.mixin Record IsCoalgebra {𝐂: BareQuiver} (F: ob 𝐂 -> ob 𝐂) (A: ob 𝐂) := {
    #[canonical=no] coalg: A ~> F A;
  }.
#[short(type="Coalgebra")]
HB.structure Definition COALGEBRA 𝐂 F := { A of IsCoalgebra 𝐂 F A }.
Arguments coalg {_ _ _}, {_ _}. 
Section s.
Context {𝐂: BareQuiver} (F: ob 𝐂 -> ob 𝐂) (A: ob 𝐂).
Definition coalgebra (a: A ~> F A) := A.
HB.instance Definition _ a := @IsCoalgebra.Build 𝐂 F (coalgebra a) a.
Definition coalgebra_ a: Coalgebra F := coalgebra a.
End s.

(** duality with algebras *)

Section s.
Context {𝐂: BareQuiver} (F: ob 𝐂 -> ob 𝐂)  (G: ob 𝐂^op -> ob 𝐂^op).
HB.instance Definition _ (A: Algebra F) :=
  IsCoalgebra.Build (𝐂^op) (funcop F) (obop A) (alg A).
HB.instance Definition _ (A: Coalgebra F) :=
  IsAlgebra.Build (𝐂^op) (funcop F) (obop A) (coalg A).
HB.instance Definition _ (A: Algebra G) :=
  IsCoalgebra.Build 𝐂 (funcop' G) (obop' A) (alg A).
HB.instance Definition _ (A: Coalgebra G) :=
  IsAlgebra.Build 𝐂 (funcop' G) (obop' A) (coalg A).
End s.

(** ** coalgebras morphisms *)

Section s.
Context {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Coalgebra F).
Definition coalghom (f: A ~> B) := coalg A \; Fhom F f ≡ f \; coalg B.
Definition Coalghom := sig coalghom. 
Coercion Coalghom_sort (f: Coalghom): A ~> B := sval f.
Definition mk_coalghom (f: A ~> B): coalghom f -> Coalghom := exist _ f. 
Definition coalgP (f: Coalghom): coalghom f := proj2_sig f.
End s.
Arguments Coalghom {_ _}.
Arguments coalghom {_} [_ _ _] _/.
Arguments mk_coalghom {_} [_ _ _] &_ _.
HB.instance Definition _ {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (Coalgebra F) Coalghom.

(** duality with algebra morphisms *)

Section s.
  Context {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (G: PreFunctor 𝐂^op 𝐂^op).
  Definition Alghomop (A B: Algebra F) (f: Alghom A B):
    Coalghom (@obop 𝐂 B) (@obop 𝐂 A) := f. 
  Definition Alghomop' (A B: Algebra G) (f: Alghom A B):
    Coalghom (@obop' 𝐂 B) (@obop' 𝐂 A) := f. 
  Definition Coalghomop (A B: Coalgebra F) (f: Coalghom A B):
    Alghom (@obop 𝐂 B) (@obop 𝐂 A) := f. 
  Definition Coalghomop' (A B: Coalgebra G) (f: Coalghom A B):
    Alghom (@obop' 𝐂 B) (@obop' 𝐂 A) := f. 
End s.

(** ** the category of coalgebras *)

Section s.
Context {𝐂: Cat} (F: Functor 𝐂 𝐂).

Definition Coalghom_id (A: Coalgebra F): A ~> A := Alghomop' (Alghom_id (@obop 𝐂 A)). 

Definition Coalghom_comp (A B C: Coalgebra F) (f: A ~> B) (g: B ~> C): A ~> C :=
  Alghomop' (Alghom_comp (Coalghomop g) (Coalghomop f)). 

HB.instance Definition _ := IsPreCat.Build (Coalgebra F) Coalghom_id Coalghom_comp.

Lemma _coalg_cat: IsCat (Coalgebra F).
Proof.
  split; intros.
  - exact/comp1o. 
  - exact/compo1. 
  - exact/compoA.
  - move=>??????. exact/comp_eqv.
Qed.
HB.instance Definition _ := _coalg_cat.

Definition Coalghom_self (A: Coalgebra F): A ~> coalgebra_ (Fhom F (coalg A)) :=
  Alghomop' (Alghom_self (@obop 𝐂 A)).

(** ** Lambek Lemma *)

Section lambek.
  (* TODO: improve insertion of coercions INITIAL.sort and Coalghom_sort *)
  Variable A: Terminal (Coalgebra F).
  Abbreviation A' := (TERMINAL.sort A). 
  Let FA: Coalgebra F := coalgebra_ (Fhom F (coalg A')).
  Let b: FA ~> A' := term A FA.
  Let ab: coalg A' \; Coalghom_sort b ≡ idmap.
  Proof. exact: (termU (Coalghom_self A' \; b) (Coalghom_id _)). Qed.
  Let ba: Coalghom_sort b \; coalg A' ≡ idmap.
  Proof. rewrite -coalgP-Fcomp ab. cat. Qed.
  HB.instance Definition _ := @IsIso.Build _ _ _ (coalg A') (Coalghom_sort b) ba ab. 
End lambek.
Check fun A: Terminal (Coalgebra F) => coalg (TERMINAL.sort A): Iso _ _. 

End s.


