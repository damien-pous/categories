(** * categories with hom-setoids *)

From PartialOrders Require Export setoid.

#[export] Set Implicit Arguments.
#[export] Unset Strict Implicit.
#[export] Unset Printing Implicit Defensive.
#[export] Unset Asymmetric Patterns.
#[export] Obligation Tactic := idtac. 

(** reserved notations *)

Reserved Notation "A ≃ B" (at level 70, format "A  ≃  B").
Reserved Notation "A ≃_ 𝐂 B" (at level 70, 𝐂 at level 0, format "A  ≃_ 𝐂  B").

Reserved Notation "a ~> b" (at level 99, b at level 200, format "a  ~>  b").
Reserved Notation "a ~>_ 𝐂 b" (at level 99, 𝐂 at level 0).

Reserved Notation "a ↪ b" (at level 99, b at level 200, format "a  ↪  b").
Reserved Notation "a ↪_ 𝐂 b" (at level 99, 𝐂 at level 0).

Reserved Notation "a ↠ b" (at level 99, b at level 200, format "a  ↠  b").
Reserved Notation "a ↠_ 𝐂 b" (at level 99, 𝐂 at level 0).

Reserved Notation "a ⥲ b" (at level 99, b at level 200, format "a  ⥲  b").
Reserved Notation "a ⥲_ 𝐂 b" (at level 99, 𝐂 at level 0).

Reserved Notation "f ∘ g" (at level 40, left associativity). 
Reserved Notation "f ∘[ 𝐂 ] g" (at level 40).

Reserved Notation "X ⊗ Y" (at level 29).

Reserved Notation "𝐂 ^op" (at level 1, format "𝐂 ^op").

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope cat_scope.


(** for temporarily admitting things *)
Axiom sorry: forall {A: Type}, A.
Ltac sorry := exact: sorry. 


(** casting morphism-like types *)
Definition ecast' {A} {T: A -> A -> Type} [a b a' b'] (x: T a b) (aa: a = a') (bb: b = b'): T a' b' :=
  eq_rect _ (fun a => T a b') (eq_rect _ _ x _ bb) _ aa.
Arguments ecast' {_ _} [_ _ _ _] _ & _ _: simpl never.
Notation ecast a' b' f := (@ecast' _ _ _ _ a' b' f _ _).

       
(** * Categories *)

(** quivers *)
#[primitive] HB.mixin Record IsQuiver 𝐂 := {
    #[canonical=no] hom : 𝐂 -> 𝐂 -> Setoid.type
  }.
#[short(type="Quiver")]
HB.structure Definition quiver := { 𝐂 of IsQuiver 𝐂 }.
Bind Scope cat_scope with Quiver.
Bind Scope cat_scope with hom.
Arguments hom {_}.
Coercion hom: Quiver >-> Funclass.
Notation "a ~> b" := (hom a b).
Notation "a ~>_ 𝐂 b" := (@hom 𝐂 a b) (only parsing) : cat_scope.
Notation bare f := (f: hom _ _). 

(** precategories: quivers + id and comp *)
#[primitive] HB.mixin Record IsPreCat 𝐂 of quiver 𝐂 := {
  #[canonical=no] idmap: forall {A: 𝐂}, A ~> A;
  #[canonical=no] comp: forall {A B C: 𝐂}, (A ~> B) -> (B ~> C) -> (A ~> C);
}.
#[short(type="PreCat")]
HB.structure Definition precat := { 𝐂 of IsPreCat 𝐂 & }.
Arguments idmap {_ _}.
Arguments comp {_ _ _ _}.
Bind Scope cat_scope with PreCat.
Notation "\idmap A" := (@idmap _ A) (only parsing, at level 0) : cat_scope.
Notation "f ∘ g" := (comp g f) : cat_scope.
Notation "f ∘[ 𝐂 ] g" := (@comp _ 𝐂 _ _ _ g f) (only parsing): cat_scope.
Notation "f \; g" := (comp f g) (only parsing): cat_scope.

(** categories: precategories + laws *)
HB.mixin Record IsCat 𝐂 of precat 𝐂 := {
  #[canonical=no] comp1o: forall {A B: 𝐂} (f: A ~> B), f ∘ idmap ≡ f;
  #[canonical=no] compo1: forall {A B: 𝐂} (f: A ~> B), idmap ∘ f ≡ f;
  #[canonical=no] compoA: forall {A B C D: 𝐂} (f: A ~> B) (g: B ~> C) (h: C ~> D),
      h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f;
  #[canonical=no] comp_eqv: forall {A B C}, Proper (eqv ==> eqv ==> eqv) (@comp 𝐂 A B C);
}.
#[short(type="Cat")]
HB.structure Definition cat := { 𝐂 of IsCat 𝐂 & }.
Bind Scope cat_scope with Cat.
Arguments compo1 {_ _ _}.
Arguments comp1o {_ _ _}.
Arguments compoA {_ _ _ _ _}.
Arguments comp_eqv {_ _ _ _}.
Existing Instance comp_eqv.

(** rewriting tuple *)
Definition cats := (@compo1, @comp1o, @compoA)%core.

(** duality: opposite category *)
Definition catop (𝐂: Type): Type := 𝐂.
Notation "𝐂 ^op" := (catop 𝐂): cat_scope.
HB.instance Definition _ (𝐂: Quiver) :=
  IsQuiver.Build 𝐂^op (fun a b => hom b a).
HB.instance Definition _ (𝐂: PreCat) :=
  IsPreCat.Build (𝐂^op) (fun=> idmap) (fun _ _ _ f g => f ∘ g).
HB.instance Definition _ (𝐂: Cat) := IsCat.Build (𝐂^op)
  (fun _ _ => compo1) 
  (fun _ _ => comp1o)
  (fun _ _ _ _ _ _ _ => eqv_sym _ _ (compoA _ _ _))
  (fun _ _ _ _ _ H _ _ H' => comp_eqv _ _ H' _ _ H).
(** key for dual morphisms *)
Definition morphop {𝐂: Quiver} [x y: 𝐂] (f: x ~> y): y ~>_(𝐂^op) x := f.

(** unit (terminal) category *)
Definition Cat1 := unit.
HB.instance Definition _ := IsQuiver.Build Cat1 (fun _ _ => unit).
HB.instance Definition _ := IsPreCat.Build Cat1 (fun _ => tt) (fun _ _ _ _ _ => tt).
HB.instance Definition _ := IsCat.Build Cat1
                              (fun _ _ _ => I) (fun _ _ _ => I)
                              (fun _ _ _ _ _ _ _ => I)
                              (fun _ _ _ _ _ _ _ _ _ => I).

(** product of categories *)
HB.instance Definition _ (𝐂 𝐃: Quiver) := IsQuiver.Build (𝐂*𝐃)%type
    (fun A B => (A.1 ~> B.1) * (A.2 ~> B.2))%type. 
HB.instance Definition _ (𝐂 𝐃: PreCat) := IsPreCat.Build (𝐂*𝐃)%type
    (fun A => (idmap,idmap))
    (fun A B C f g => (g.1 ∘ f.1, g.2 ∘ f.2)).
Program Definition _prod_cat (𝐂 𝐃: Cat) := IsCat.Build (𝐂*𝐃)%type _ _ _ _. 
Next Obligation. split; apply: comp1o. Qed.
Next Obligation. split; apply: compo1. Qed.
Next Obligation. split; apply: compoA. Qed.
Next Obligation. move=>*??[??]??[??]. split=>/=; exact: comp_eqv. Qed.
HB.instance Definition _ 𝐂 𝐃 := _prod_cat 𝐂 𝐃. 


(** * Unique existence *)

(** in Setoids *)

Record Unique [T: Setoid.type] (P : T -> Type) := {
    unique_elt: T;
    unique_prop: P unique_elt;
    uniqueness: forall x : T, P x -> unique_elt ≡ x;
  }.
Arguments unique_elt {_ _}.
Arguments unique_prop {_ _}.
Arguments uniqueness {_ _}.

Notation "' u" := (unique_prop u) (at level 100).
Notation "'' u" := (uniqueness u) (at level 100).

(** of morphisms *)

Section s.
Context {𝐂: Quiver} [A B: 𝐂] (P: (A ~> B) -> Type).
          
Definition Unique_morph := Unique P.

Lemma Unicity: Unique_morph -> forall (u v: A ~> B), P u -> P v -> u ≡ v.
Proof.
  intros [w _ U] u v Pu Pv.
  by rewrite -(U _ Pu) (U _ Pv). 
Qed.

Definition unique_morph: Unique P -> A ~> B := unique_elt.

End s.
Arguments unique_morph {_ _ _ _}.
Arguments Unicity {_ _ _ _}.

Notation "∃! x .. y , P" := (Unique_morph (fun x => .. (Unique_morph (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : cat_scope.

Lemma unique_morph_eqv {𝐂: Quiver} [A B: 𝐂] (P Q: (A ~> B) -> Type):
  (forall f, P f -> Q f) -> forall p: Unique_morph P, forall q: Unique_morph Q, unique_morph p ≡ unique_morph q.
Proof.
  move=>PQ p q. apply: Unicity. eassumption.
  apply: PQ. all: exact: unique_prop.
Qed.

(** * Isomorphisms *)

HB.mixin Record IsIso (𝐂: PreCat) A B (f: 𝐂 A B) := {
    #[canonical=no] inverse: 𝐂 B A;
    #[canonical=no] isoK: f ∘ inverse ≡ idmap;
    #[canonical=no] isoK': inverse ∘ f ≡ idmap }.
#[short(type="Iso")]
HB.structure Definition iso 𝐂 A B := { f of @IsIso 𝐂 A B f }.
Arguments inverse {_ _ _}.
Arguments isoK {_ _ _}.
Arguments isoK' {_ _ _}.
Notation "A ≃_ 𝐂 B" := (@iso.type 𝐂 A B) (only parsing).
Notation "A ≃ B" := (Iso A B).

Definition mk_iso {𝐂: PreCat} {X Y: 𝐂} (i: X ~> Y) (j: Y ~> X): i ∘ j ≡ idmap -> j ∘ i ≡ idmap -> X ≃ Y.
Proof. move=>ij ji. exists i. split. by exists j. Defined. 
Arguments mk_iso {_ _ _}. 

(** forward and backward components *)
Definition forward {𝐂: PreCat} [A B: 𝐂] (i: Iso A B) := bare i.
Notation "f '¹'" := (forward f) (at level 9, format "f '¹'").
Notation "f '⁻¹'" := (inverse f) (at level 9, format "f '⁻¹'").

Section s.
Context {𝐂: Cat}.
Implicit Types A B C: 𝐂.

(** isomorphisms form a groupoid *)
Lemma _iso_id A: IsIso _ A A idmap.
Proof. exists idmap. exact: compo1. exact: comp1o. Defined.
Lemma _iso_comp A B C (f: A ≃ B) (g: B ≃ C): IsIso _ A C (g ∘ f).
Proof.
  exists (f⁻¹ ∘ g⁻¹).
  abstract (by rewrite compoA -(compoA f⁻¹) isoK comp1o isoK).
  abstract (by rewrite -compoA (compoA f) isoK' compo1 isoK').
Defined.

HB.instance Definition _ A := _iso_id A. 
HB.instance Definition _ A B C (f: A ≃ B) (g: B ≃ C) := _iso_comp f g. 
HB.instance Definition _ A B (i: A ≃ B) := @IsIso.Build _ B A (i⁻¹) (i¹) (isoK' i) (isoK i). 

Definition iso_refl A: A ≃ A := idmap.
Definition iso_trans A B C (i: A ≃ B) (j: B ≃ C): A ≃ C := j ∘ i.
Definition iso_sym A B (i: A ≃ B): B ≃ A := i⁻¹. 

Lemma iso_switch_src_r A A' B (f: A ~> B) (g: A' ~> B) (i: A ≃ A'): f ≡ g ∘ i <-> f ∘ i⁻¹ ≡ g.
Proof.
  split.
  - move=>->. by rewrite -compoA isoK cats.
  - move=><-. by rewrite -compoA isoK' cats.
Qed.

Lemma iso_switch_tgt_r A B B' (f: A ~> B) (g: A ~> B') (i: B' ≃ B): f ≡ i ∘ g <-> i⁻¹ ∘ f  ≡ g.
Proof.
  split.
  - move=>->. by rewrite compoA isoK' cats.
  - move=><-. by rewrite compoA isoK cats.
Qed.

Lemma iso_switch_src_l A A' B (f: A ~> B) (g: A' ~> B) (i: A' ≃ A): f ∘ i ≡ g <-> f ≡ g ∘ i⁻¹.
Proof. split=>H; exact/eqv_sym/iso_switch_src_r/eqv_sym. Qed.

Lemma iso_switch_tgt_l A B B' (f: A ~> B) (g: A ~> B') (i: B ≃ B'): i ∘ f ≡ g <-> f  ≡ i⁻¹ ∘ g.
Proof. split=>H; exact/eqv_sym/iso_switch_tgt_r/eqv_sym. Qed.

End s. 
Definition iso_switch :=
  (@iso_switch_src_l, @iso_switch_src_r, @iso_switch_tgt_l, @iso_switch_tgt_r)%core.
