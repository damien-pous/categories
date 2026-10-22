(** * cospans *)

Require Import cat morphisms span (* shape functor adjunction colimit *).

Local Open Scope cat_scope.

(** ** cospans *)

#[primitive] HB.mixin Record IsCospan (𝐂: BareQuiver) (a b: ob 𝐂) (x: ob 𝐂) := {
    #[canonical=no] in1: a ~> x;
    #[canonical=no] in2: b ~> x;
  }.
#[short(type=Cospan)]
HB.structure Definition COSPAN 𝐂 a b := {x of IsCospan 𝐂 a b x}. 

Section s.
Context {𝐂: BareQuiver} (a b: ob 𝐂).

Definition cospan (x: ob 𝐂) (f: a ~> x) (g: b ~> x) := x.
HB.instance Definition _ x f g := IsCospan.Build 𝐂 a b (@cospan x f g) f g.
Definition cospan_ (x: ob 𝐂) (f: a ~> x) (g: b ~> x): Cospan a b := cospan f g.

Definition cospanC (x: Cospan a b): ob 𝐂 := x.
HB.instance Definition _ x := IsCospan.Build 𝐂 b a (cospanC x) in2 in1.

(** duality with spans *)
HB.instance Definition _ (x: Span a b) := IsCospan.Build 𝐂^op (obop a) (obop b) (obop x) pi1 pi2. 
HB.instance Definition _ (x: Span (obop a) (obop b)) := IsCospan.Build 𝐂 a b (obop' x) (pi1 (s:=x)) (pi2 (s:=x)).
HB.instance Definition _ (x: Cospan a b) := IsSpan.Build 𝐂^op (obop a) (obop b) (obop x) in1 in2.
HB.instance Definition _ (x: Cospan (obop a) (obop b)) := IsSpan.Build 𝐂 a b (obop' x) (in1 (s:=x)) (in2 (s:=x)).

End s.

(** ** cospan homomorphisms *)

Section s.
Context {𝐂: PreCat}.
Implicit Types a b: ob 𝐂.

Definition cospanhom a b (x y: ob 𝐂) (x1: a ~> x) (x2: b ~> x) (y1: a ~> y) (y2: b ~> y) (f: x ~> y) :=
  x1 \; f ≡ y1 ∧ x2 \; f ≡ y2.
Definition Cospanhom {a b} (x y: Cospan a b) := sig (fun f: x ~> y => cospanhom in1 in2 in1 in2 f).
Coercion Cospanhom_sort a b x y (f: @Cospanhom a b x y): x ~> y := sval f.
Definition CospanH a b x y (f: @Cospanhom a b x y): in1 \; f ≡ in1 ∧ in2 \; f ≡ in2 := proj2_sig f.
HB.instance Definition _ a b := IsQuiver.Build (Cospan a b) Cospanhom.

Definition cospan_homC a b (x y: Cospan a b) (f: Cospanhom x y): Cospanhom (cospanC x) (cospanC y).
Proof. exists f. abstract exact/swap_pair/(CospanH f). Defined.
Definition cospan_homC' a b (x y: Cospan b a) (f: Cospanhom (cospanC x) (cospanC y)): Cospanhom x y.
Proof. exact: (cospan_homC f). Defined.
Definition cospan_homC1 a b (x: Cospan b a) (y: Cospan a b) (f: Cospanhom (cospanC x) y): Cospanhom x (cospanC y).
Proof. exact: (cospan_homC f). Defined.
Definition cospan_homC2 a b (x: Cospan a b) (y: Cospan b a) (f: Cospanhom x (cospanC y)): Cospanhom (cospanC x) y.
Proof. exact: (cospan_homC f). Defined.

End s.
Arguments cospanhom {_} [_ _ _ _] _ _ _ _ _/.


(** duality with span homomorphisms *)

Section s.
Context {𝐂: PreCat}.
Definition Spanhomop (a b: ob 𝐂) (x y: Span a b) (f: Spanhom x y):
  Cospanhom (obop (y: ob 𝐂)) (obop (x: ob 𝐂)) := f. 
Definition Spanhomop' (a b: ob 𝐂^op) (x y: Span a b) (f: Spanhom x y):
  Cospanhom (@obop' 𝐂 y) (@obop' 𝐂 x) := f. 
Definition Cospanhomop (a b: ob 𝐂) (x y: Cospan a b) (f: Cospanhom x y):
  Spanhom (obop (y: ob 𝐂)) (obop (x: ob 𝐂)) := f. 
Definition Cospanhomop' (a b: ob 𝐂^op) (x y: Cospan a b) (f: Cospanhom x y):
  Spanhom (@obop' 𝐂 y) (@obop' 𝐂 x) := f. 
End s.

(** ** the category of cospans *)

Section s.
Context {𝐂: Cat} (a b: ob 𝐂).

Definition Cospan_id (x: Cospan a b): hom x x := Span_id (obop (x: ob 𝐂)).
Definition Cospan_comp (x y z: Cospan a b) (f: hom x y) (g: hom y z): hom x z :=
  Span_comp (Cospanhomop g) (Cospanhomop f). 
HB.instance Definition _ := IsPreCat.Build (Cospan a b) Cospan_id Cospan_comp. 

Lemma _cospan_cat: IsCat (Cospan a b).
Proof.
  split=>*.
  - exact: comp1o. 
  - exact: compo1. 
  - exact: compoA. 
  - intros??????; exact: comp_eqv.
Qed.
HB.instance Definition _ := _cospan_cat.

Definition Cospaniso_sort (x y: Cospan a b) (i: x ≃ y): x ≃_𝐂 y :=
  iso_ (Cospanhom_sort i¹) (Cospanhom_sort i⁻¹) (invKl i) (invKr i). 

Lemma cospanhom_inv (x y: Cospan a b) (i: x ≃_𝐂 y) (H: cospanhom in1 in2 in1 in2 i¹):
  cospanhom in1 in2 in1 in2 i⁻¹.
Proof. by split; rewrite iso_tgt H. Qed.

Definition cospaniso_ (x y: Cospan a b) (i: x ≃_𝐂 y) (H: cospanhom in1 in2 in1 in2 i¹): x ≃ y :=
  @iso_ _ x y (exist _ i¹ H) (exist _ i⁻¹ (cospanhom_inv H)) (invKl i) (invKr i).

End s.
