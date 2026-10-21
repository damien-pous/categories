(** * coalgebras *)

Require Export algebra.
Require Import arewrite.

Local Open Scope cat_scope.

(** ** coalgebras *)

#[primitive]
HB.mixin Record IsCoalgebra {𝐂: BareQuiver} (F: FUN 𝐂 𝐂) (A: ob 𝐂) := {
    #[canonical=no] coalg: A ~> F A;
  }.
#[short(type="Coalgebra")]
HB.structure Definition COALGEBRA 𝐂 F := { A of IsCoalgebra 𝐂 F A }.
Arguments coalg {_ _ _}, {_ _}. 
Section s.
Context {𝐂: BareQuiver} (F: FUN 𝐂 𝐂) (A: ob 𝐂).
Definition coalgebra (a: A ~> F A) := A.
HB.instance Definition _ a := @IsCoalgebra.Build 𝐂 F (coalgebra a) a.
Definition coalgebra_ a: Coalgebra F := coalgebra a.
End s.

(** duality with algebras *)

Section s.
Context {𝐂: BareQuiver} (F: FUN 𝐂 𝐂)  (G: FUN 𝐂^op 𝐂^op).
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

Definition is_coalghom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Coalgebra F) (f: A ~> B) :=
  coalg A \; Fhom F f ≡ f \; coalg B.
Arguments is_coalghom {_} [_ _ _] _/.
#[primitive]
HB.mixin Record IsCoalghom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Coalgebra F) (f: A ~> B) := {
    #[canonical=no] coalghomP: is_coalghom f;
  }.
#[short(type="Coalghom")]
HB.structure Definition COALGHOM 𝐂 F A B := { f of IsCoalghom 𝐂 F A B f }.
Arguments Coalghom {_ _}.
HB.instance Definition _ 𝐂 F A B := Setoid.copy (Coalghom A B) (kernel (@COALGHOM.sort 𝐂 F A B)).
Section s.
Context {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Coalgebra F).
Definition coalghom (f: A ~> B) (H: is_coalghom f) := f.  
HB.instance Definition _ f H := IsCoalghom.Build 𝐂 F A B (@coalghom f H) H.
Definition coalghom_ (f: A ~> B) (H: is_coalghom f): Coalghom A B := coalghom H.  
End s.
Arguments coalghom {_} [_ _ _] _ _.
Arguments coalghom_ {_} [_ _ _] _ _.

(** duality with algebra morphisms *)

Section s.
  Context {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (G: PreFunctor 𝐂^op 𝐂^op).
  HB.instance Definition _ (A B: Algebra F) (f: Alghom A B):=
    IsCoalghom.Build 𝐂^op (funcop F) (@obop 𝐂 B) (@obop 𝐂 A) (morphop f) alghomP. 
  HB.instance Definition _ (A B: Algebra G) (f: Alghom A B):=
    IsCoalghom.Build 𝐂 (funcop' G) (@obop' 𝐂 B) (@obop' 𝐂 A) (morphop' f) (alghomP (s:=f)). 
  HB.instance Definition _ (A B: Coalgebra F) (f: Coalghom A B):=
    IsAlghom.Build 𝐂^op (funcop F) (@obop 𝐂 B) (@obop 𝐂 A) (morphop f) coalghomP. 
  HB.instance Definition _ (A B: Coalgebra G) (f: Coalghom A B):=
    IsAlghom.Build 𝐂 (funcop' G) (@obop' 𝐂 B) (@obop' 𝐂 A) (morphop' f) (coalghomP (s:=f)). 
End s.

(** ** the category of coalgebras *)

HB.instance Definition _ {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (Coalgebra F) Coalghom.

Section s.
Context {𝐂: Cat} (F: Functor 𝐂 𝐂).
Implicit Types A B C: Coalgebra F.   

Lemma coalghom_id A: is_coalghom A.
Proof. exact: (alghom_id (@obop 𝐂 A)). Qed.
HB.instance Definition _ A := IsCoalghom.Build 𝐂 F A A A (coalghom_id A).
Definition Coalghom_id {A}: Coalghom A A := A. 

Lemma coalghom_comp A B C (f: Coalghom A B) (g: Coalghom B C): is_coalghom (f \; g).
Proof. exact: (alghom_comp (morphop g) (morphop f)). Qed.
HB.instance Definition _ A B C (f g: Coalghom _ _) := IsCoalghom.Build 𝐂 F A C (f \; g) (@coalghom_comp A B C f g).
Definition Coalghom_comp {A B C} (f g: Coalghom _ _): Coalghom A C := @comp _ A B C f g. 

HB.instance Definition _ := IsPreCat.Build (Coalgebra F) (@Coalghom_id) (@Coalghom_comp).

Lemma _coalg_cat: IsCat (Coalgebra F).
Proof.
  split; intros.
  - exact/comp1o. 
  - exact/compo1. 
  - exact/compoA.
  - move=>??????. exact/comp_eqv.
Qed.
HB.instance Definition _ := _coalg_cat.

Definition coalgnext A := F A.
HB.instance Definition _ A := IsCoalgebra.Build 𝐂 F (coalgnext A) (Fhom F (coalg A)).
Definition coalgnexthom A: A ~>_𝐂 coalgnext A := coalg A.
HB.instance Definition _ A := IsCoalghom.Build 𝐂 F A (coalgnext A) (coalgnexthom A) eqv_refl.
Definition coalgnexthom_ A: Coalghom A (coalgnext A) := coalgnexthom A.

(** ** Lambek Lemma *)

Section lambek.
  (* TODO: improve insertion of coercions INITIAL.sort and Alghom_sort *)
  (* TODO: get it by duality (probably needs an explicit one) *)
  Variable A: Terminal (Coalgebra F).
  Abbreviation A' := (TERMINAL.sort A). 
  Abbreviation FA := (coalgnext A': Coalgebra F). 
  Let b: FA ~> A' := term A FA.
  (*
FA -Fb-> FFA -Fa-> FA
|a       |Fa       |a
V        V         V
A --b--> FA --a--> A
   *)
  Let ab: coalg A' \; b ≡ idmap.
  Proof. exact: (@termU _ A _ (Coalghom_comp (coalgnexthom_ A') b) idmap). Qed.
  Let ba: COALGHOM.sort b \; coalg A'  ≡ idmap.
  Proof. rewrite -coalghomP-Fcomp ab. cat. Qed.
  HB.instance Definition _ := @IsIso.Build _ _ _ (coalg A') b ba ab. 
End lambek.
Check fun A: Terminal (Coalgebra F) => coalg (TERMINAL.sort A): Iso _ _. 

End s.


