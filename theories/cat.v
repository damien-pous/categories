(** * categories with hom-setoids *)

From PartialOrders Require Export setoid.
From elpi Require Import elpi coercion.

#[export] Set Implicit Arguments.
#[export] Unset Strict Implicit.
#[export] Unset Printing Implicit Defensive.
#[export] Unset Asymmetric Patterns.
#[export] Obligation Tactic := idtac. 

(** ** reserved notations *)

(** morphisms, monos, epis, isos *)

Reserved Notation "a ~> b" (at level 99, b at level 200, format "a  ~>  b").
Reserved Notation "a ~>_ 𝐂 b" (at level 99, 𝐂 at level 0).

Reserved Notation "a ↪ b" (at level 99, b at level 200, format "a  ↪  b").
Reserved Notation "a ↪_ 𝐂 b" (at level 99, 𝐂 at level 0).

Reserved Notation "a ↠ b" (at level 99, b at level 200, format "a  ↠  b").
Reserved Notation "a ↠_ 𝐂 b" (at level 99, 𝐂 at level 0).

Reserved Notation "A ≃ B" (at level 70, format "A  ≃  B").
Reserved Notation "A ≃_ 𝐂 B" (at level 70, 𝐂 at level 0, format "A  ≃_ 𝐂  B").

Reserved Notation "a ⥲ b" (at level 99, b at level 200, format "a  ⥲  b").
Reserved Notation "a ⥲_ 𝐂 b" (at level 99, 𝐂 at level 0).
(** natural isomorphisms *)
Reserved Notation "F ≈ G" (at level 70).

(** composition *)
Reserved Notation "f ∘ g" (at level 40, left associativity). 
Reserved Notation "f ∘[ 𝐂 ] g" (at level 40).

(** tensor (in monoidal categories) *)
Reserved Notation "X ⊗ Y" (at level 31, right associativity). (* objects *)
Reserved Notation "f · g" (at level 30, right associativity). (* morphisms *)
Reserved Notation "n ⊚ m" (at level 30, right associativity). (* natural transformations *)

(** opposite category *)
Reserved Notation "𝐂 ^op" (at level 1, format "𝐂 ^op").

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope cat_scope.


(** for temporarily admitting things *)
Axiom sorry: forall {A: Type}, A.
Ltac sorry := exact: sorry. 


(** casting morphism-like types *)
Definition cast2' {A} {T: A -> A -> Type} [a b a' b'] (x: T a b) (aa: a = a') (bb: b = b'): T a' b' :=
  eq_rect _ (fun a => T a b') (eq_rect _ _ x _ bb) _ aa.
Arguments cast2' {_ _} [_ _ _ _] _ & !_ !_.
Notation cast2 a' b' f := (@cast2' _ _ _ _ a' b' f _ _).

       
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
#[primitive] HB.mixin Record IsCat 𝐂 of precat 𝐂 := {
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

(** tweaking coercions so that objects can always be seen as identity morphisms *)
Elpi Accumulate coercion.db lp:"
coercion _ V T E R :- coq.unify-eq T {{precat.sort _}} ok, coq.unify-eq E {{Setoid.sort _}} ok, !, R = {{@idmap _ lp:V}}.
".
(* Check fun C: Cat => fun A: C => A: A ~> A. *)

(** (locally) import this module to get the underlying object printed instead of [idmap] *)
Module SEEOBJ.
  Coercion idmap: precat.sort >-> Setoid.sort.
End SEEOBJ.
(* Import SEEOBJ. *)
(* Check fun C: Cat => fun A: C => A: A ~> A. *)

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

Program Definition pair_iso {𝐂 𝐃: Cat} {A A' B B'} (i: A ≃_𝐂 A') (j: B ≃_𝐃 B'):
  (A,B) ≃_((𝐂*𝐃)%type) (A',B') :=
  @mk_iso (𝐂*𝐃)%type (A,B) (A',B') (i¹,j¹) (i⁻¹,j⁻¹) _ _.
Next Obligation. split; exact: isoK. Qed.
Next Obligation. split; exact: isoK'. Qed.

(** ** extensible normalisation tactic via canonical structures *)
Module HL.
Section s.
Context {𝐂: Cat}.
Implicit Types A B C: 𝐂.
Inductive hom_list_ C: 𝐂 -> Type :=
| nil: hom_list_ C C
| cons: forall {A B}, (A ~> B) -> hom_list_ C B -> hom_list_ C A.
Notation hom_list A B := (hom_list_ B A).
Arguments nil {_}. 
Definition single {A B} (f: A ~> B) := cons f nil. 
Fixpoint eval {B C} (u: hom_list B C): B ~> C :=
  match u with
  | nil => idmap
  | cons g u => 
      match u with
      | nil => fun g => g
      | _ => fun _ => g \; eval u
      end g
  end.
Fixpoint app {A B} (u: hom_list A B): forall {C}, hom_list B C -> hom_list A C :=
  match u with
  | nil => fun _ v => v
  | cons f u => fun _ v => cons f (app u v)
  end.
Lemma eval_nil {A}: eval (@nil A) ≡ idmap.
Proof. done. Qed.
Lemma eval_cons {A B C} f u: eval (@cons C A B f u) ≡ f \; eval u.
Proof. revert A f. case: u=>//= A f. by rewrite compo1. Qed.
Lemma eval_single {A B} (f: A~>B): eval (single f) ≡ f.
Proof. by rewrite eval_cons eval_nil compo1. Qed.
Lemma eval_app {A B C} u v: eval (@app A B u C v) ≡ eval u \; eval v.
Proof.
  revert C v. elim: u=>[|B' C' f u IH] C v; simpl app.
  by rewrite eval_nil comp1o.
  by rewrite 2!eval_cons IH compoA.
Qed.
  
Structure reified A B := reify {
    term:> A ~> B;
    #[canonical=no] norm: hom_list A B;
    #[canonical=no] normE: eval norm ≡ term;
}.
Arguments reify {_ _}.
Definition r_id {A} := reify (\idmap A) nil eval_nil.
Program Definition r_comp {A B C} (u: reified A B) (v: reified B C) :=
  reify (u \; v) (app (norm u) (norm v)) _.
Next Obligation. intros. by rewrite eval_app 2!normE. Qed.
Definition r_var {A B} (f: A~>B) := reify f (single f) (eval_single f).

Lemma cats' {a b} (u v: reified a b):
  term u ≡ term v <-> eval (norm u) ≡ eval (norm v).
Proof. by rewrite 2!normE. Qed.

Lemma normalise {A B} (u v: reified A B): eval (norm u) ≡ eval (norm v) -> u ≡ v.
Proof. apply cats'. Qed.

End s.
Notation hom_list A B := (hom_list_ B A).
Arguments nil {_ _}.
Arguments reify {_ _ _}.
Program Definition r_sym1 {𝐂 𝐃: Cat} {A B: 𝐂} {A' B': 𝐃}
  (f: (A~>B) -> (A'~>B')) (Hf: Proper (eqv ==> eqv) f)
  (u: reified A B) := reify (f u) (single (f (eval (norm u)))) _.
Next Obligation. intros. by rewrite eval_single normE. Qed.
Definition r_ext {𝐂 𝐃: Cat} {A B: 𝐂} {A' B': 𝐃}
  (f: (A~>B) -eqv-> (A'~>B')) := Eval hnf in r_sym1 (extensional f).
Program Definition r_sym2 {𝐂 𝐃 𝐄: Cat} {A B: 𝐂} {A' B': 𝐃} {A'' B'': 𝐄}
  (f: (A~>B) -> (A'~>B') -> (A''~>B'')) (Hf: Proper (eqv ==> eqv ==> eqv) f)
  (u: reified A B) (v: reified A' B') := reify (f u v) (single (f (eval (norm u)) (eval (norm v)))) _.
Next Obligation. intros. by rewrite eval_single 2!normE. Qed.
Arguments r_sym1 {_ _ _ _ _ _}.
Arguments r_sym2 {_ _ _ _ _ _ _ _ _}.
End HL.
Canonical HL.r_id. 
Canonical HL.r_comp. 
Canonical HL.r_var. 
Canonical HL.r_ext. 
Ltac normalise := apply: HL.normalise; simpl HL.eval.
Ltac cat := exact: HL.normalise.
Definition cats' := @HL.cats'.

Goal forall (C: Cat) A (f: C A A), idmap ∘ f ∘ (idmap ∘ f) ∘ f ≡ f ∘ (idmap ∘ f) ∘ (idmap ∘ f).
  intros. normalise. reflexivity.
  Restart.
  intros. by cat. 
  Restart.
  intros. rewrite cats'/=. reflexivity. 
Qed.
