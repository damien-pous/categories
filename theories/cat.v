(** * categories with hom-setoids *)
Require Export prelim.
From elpi Require Import elpi coercion.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Local Open Scope cat_scope.

       
(** * Categories *)

(** quivers *)
#[primitive] HB.mixin Record IsBareQuiver 𝐂 := {
    #[canonical=no] hom: ob 𝐂 -> ob 𝐂 -> Type
}.
#[short(type="BareQuiver")]
HB.structure Definition barequiver := { 𝐂 of IsBareQuiver 𝐂 }.
Bind Scope cat_scope with hom.
Arguments hom {_}.
Coercion hom: BareQuiver >-> Funclass.
Notation "a ~> b" := (hom a b): cat_scope.
Notation "a ~>_ 𝐂 b" := (@hom 𝐂 a b) (only parsing): cat_scope.
Abbreviation bare f := (f: hom _ _). 

(** precategories: quivers + id and comp *)
#[primitive] HB.mixin Record IsPreCat 𝐂 of barequiver 𝐂 := {
    #[canonical=no] _idmap: forall (a: ob 𝐂), a ~> a;
    #[canonical=no] _comp: forall (a b c: ob 𝐂), (a ~> b) -> (b ~> c) -> (a ~> c);
}.
#[short(type="BarePreCat")]
  HB.structure Definition bareprecat := { 𝐂 of IsPreCat 𝐂 & }.
Coercion idmap {𝐂: BarePreCat} (a: ob 𝐂): a ~> a := _idmap a.
Arguments idmap {_ _}, {_}.
Definition comp {𝐂: BarePreCat} (a b c: ob 𝐂) (f: a ~> b) (g: b ~> c): a ~> c := _comp _ _ _ f g.
Arguments comp {_ _ _ _}.
Notation "f \; g" := (comp f g): cat_scope.
Notation "f \;_ 𝐂 g" := (@comp _ 𝐂 _ _ _ f g) (only parsing): cat_scope.
Notation "f ∘ g" := (comp g f) (only parsing): cat_scope.
Notation "f ∘_ 𝐂 g" := (@comp _ 𝐂 _ _ _ g f) (only parsing): cat_scope.

(* Check fun C: Cat => fun A: ob C => A: A ~> A. *)
Module HIDEOBJ.
  Abbreviation idmap := (@idmap _ _).
  (* Check fun C: Cat => fun A: ob C => A: A ~> A. *)
End HIDEOBJ.

(** setoid enriched quivers *)
#[primitive] HB.mixin Record HomSetoids 𝐂 of barequiver 𝐂  := {
    #[canonical=no] hom_setoid: forall a b: ob 𝐂, Setoid.axioms_ (hom a b)
}.
#[short(type="Quiver")]
HB.structure Definition quiver := { 𝐂 of HomSetoids 𝐂 & }.
HB.instance Definition _ (𝐂: Quiver) (a b: ob 𝐂) := hom_setoid a b. 

HB.factory Record IsQuiver 𝐂 := {
    hom: ob 𝐂 -> ob 𝐂 -> Setoid.type
}.
HB.builders Context 𝐂 of IsQuiver 𝐂.
  HB.instance Definition _ := IsBareQuiver.Build 𝐂 hom. 
  HB.instance Definition _ := HomSetoids.Build 𝐂 (fun a b => Setoid.class (hom a b)). 
HB.end.

#[short(type="PreCat")]
HB.structure Definition precat := { 𝐂 of quiver 𝐂 & bareprecat 𝐂 }.

(** enable coercions [T >-> hom] to be used when expecting a setoid value *)
Fail Check fun (C: PreCat) (a: ob C) => a ≡ a.
Elpi Accumulate coercion.db lp:{{
      coercion _ V _ {{Setoid.sort _}} R :-
      coq.elaborate-skeleton V {{hom _ _}} R ok.
}}.
Check fun (C: PreCat) (a: ob C) => a ≡ a.
Module _test.
  Parameters (C: PreCat) (a: ob C) (T: Type) (f: T -> (a ~> a)).
  Coercion f: T >-> hom.
  Check fun t: T => t ≡ t. 
End _test.


(** categories: precategories + laws *)
#[primitive] HB.mixin Record IsCat 𝐂 of precat 𝐂 := {
    #[canonical=no] _comp1o: forall {a b: ob 𝐂} (f: a ~> b), idmap \; f ≡ f;
    #[canonical=no] _compo1: forall {a b: ob 𝐂} (f: a ~> b), f \; idmap ≡ f;
    #[canonical=no] _compoA: forall {a b c d: ob 𝐂} (f: a ~> b) (g: b ~> c) (h: c ~> d), (f \; g) \; h ≡ f \; (g \; h);
    #[canonical=no] _comp_eqv: forall {a b c}, Proper (eqv ==> eqv ==> eqv) (@comp 𝐂 a b c);
}.
#[short(type="Cat")]
HB.structure Definition cat := { 𝐂 of IsCat 𝐂 & }.
Bind Scope cat_scope with Cat.
Definition comp1o {𝐂: Cat} {a b: ob 𝐂} (f: a ~> b): idmap \; f ≡ f := _comp1o _ _ f. 
Definition compo1 {𝐂: Cat} {a b: ob 𝐂} (f: a ~> b): f \; idmap ≡ f := _compo1 _ _ f. 
Definition compoA {𝐂: Cat} {a b c d: ob 𝐂} (f: a ~> b) (g: b ~> c) (h: c ~> d): (f \; g) \; h ≡ f \; (g \; h):= _compoA _ _ _ _ f g h. 
Instance comp_eqv {𝐂: Cat} {a b c: ob 𝐂}: Proper (eqv ==> eqv ==> eqv) (@comp 𝐂 a b c) :=
  _comp_eqv a b c.


(** rewriting tuple *)
Definition cats := (@compo1, @comp1o, @compoA)%core.

(** duality: opposite category *)
Definition catop (𝐂: Type): Type := 𝐂.
Notation "𝐂 ^op" := (catop 𝐂): cat_scope.
HB.instance Definition _ (𝐂: BareQuiver) :=
  IsBareQuiver.Build 𝐂^op (fun a b => hom b a).
HB.instance Definition _ (𝐂: Quiver) :=
  HomSetoids.Build 𝐂^op (fun a b => Setoid.class (hom a b)).
HB.instance Definition _ (𝐂: PreCat) :=
  IsPreCat.Build (𝐂^op) (fun=> idmap) (fun _ _ _ f g => f ∘ g).
HB.instance Definition _ (𝐂: Cat) := IsCat.Build (𝐂^op)
  (fun _ _ => compo1) 
  (fun _ _ => comp1o)
  (fun _ _ _ _ _ _ _ => eqv_sym _ _ (compoA _ _ _))
  (fun _ _ _ _ _ H _ _ H' => comp_eqv H' H).
(** key for dual objects  *)
Definition obop (𝐂: BareQuiver) (A: ob 𝐂): ob (𝐂^op) := A. 
(** key for dual morphisms *)
Definition morphop {𝐂: BareQuiver} [x y: ob 𝐂] (f: x ~> y): obop y ~> obop x := f.

(** unit (terminal) category *)
Definition Cat1 := unit.
HB.instance Definition _ := IsQuiver.Build Cat1 (fun _ _ => unit).
HB.instance Definition _ := IsPreCat.Build Cat1 (fun _ => tt) (fun _ _ _ _ _ => tt).
HB.instance Definition _ := IsCat.Build Cat1
                              (fun _ _ _ => erefl) (fun _ _ _ => erefl)
                              (fun _ _ _ _ _ _ _ => erefl)
                              (fun _ _ _ _ _ _ _ _ _ => erefl).

(** product of categories *)
HB.instance Definition _ (𝐂 𝐃: BareQuiver) := IsBareQuiver.Build (𝐂*𝐃)%type
    (fun A B => (A.1 ~> B.1) * (A.2 ~> B.2))%type. 
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

(* TODO: move to partialorders lib *)
Record Unique [T: Setoid.type] (P : T -> Type) := {
    unique_elt: T;
    unique_prop: P unique_elt;
    uniqueness: forall x : T, P x -> unique_elt ≡ x;
  }.
Arguments unique_elt {_ _}.
Arguments unique_prop {_ _}.
Arguments uniqueness {_ _}.

(** of morphisms *)

Section s.
Context {𝐂: Quiver} [A B: ob 𝐂] (P: (A ~> B) -> Type).
          
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

Notation "Σ! x .. y , P" := (Unique_morph (fun x => .. (Unique_morph (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity): cat_scope.

Lemma unique_morph_eqv {𝐂: Quiver} [A B: ob 𝐂] (P Q: (A ~> B) -> Type):
  (forall f, P f -> Q f) -> forall p: Unique_morph P, forall q: Unique_morph Q, unique_morph p ≡ unique_morph q.
Proof.
  move=>PQ p q. apply: Unicity. eassumption.
  apply: PQ. all: exact: unique_prop.
Qed.



(** ** extensible normalisation tactic via canonical structures *)
Module HL.
Section s.
Context {𝐂: Cat}.
Implicit Types A B C: ob 𝐂.
Inductive hom_list_ C: ob 𝐂 -> Type :=
| nil: hom_list_ C C
| cons: forall {A B}, (A ~> B) -> hom_list_ C B -> hom_list_ C A.
Abbreviation hom_list A B := (hom_list_ B A).
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
Definition r_id {A} := reify (idmap A) nil eval_nil.

Program Definition r_comp {A B C} (u: reified A B) (v: reified B C) :=
  reify (u \; v) (app (norm u) (norm v)) _.
Next Obligation. intros. by rewrite eval_app 2!normE. Qed.
Definition r_var {A B} (f: A~>B) := reify f (single f) (eval_single f).

Lemma cats' {a b} (u v: reified a b):
  term u ≡ term v <-> eval (norm u) ≡ eval (norm v).
Proof. by rewrite 2!normE. Qed.

Lemma normalise {A B} (u v: reified A B): eval (norm u) ≡ eval (norm v) -> term u ≡ term v.
Proof. apply cats'. Qed.

End s.
Abbreviation hom_list A B := (hom_list_ B A).
Arguments nil {_ _}.
Arguments reify {_ _ _}.

(** helpers to declare additional symbols under which normalisation should occur *)
Program Definition r_sym1 {𝐂 𝐃: Cat} {A B: ob 𝐂} {A' B': ob 𝐃}
  (f: (A~>B) -> (A'~>B')) (Hf: Proper (eqv ==> eqv) f)
  (u: reified A B) := reify (f u) (single (f (eval (norm u)))) _.
Next Obligation. intros. by rewrite eval_single normE. Qed.
Definition r_ext {𝐂 𝐃: Cat} {A B: ob 𝐂} {A' B': ob 𝐃}
  (f: (A~>B) -eqv-> (A'~>B')) := Eval hnf in r_sym1 (extensional f).
Program Definition r_sym2 {𝐂 𝐃 𝐄: Cat} {A B: ob 𝐂} {A' B': ob 𝐃} {A'' B'': ob 𝐄}
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

(** end-user normalisation and decision tactics *)
Ltac normalise := apply: HL.normalise; simpl HL.eval.
Ltac cat := exact: HL.normalise.
Definition cats' := @HL.cats'.

(** tests *)
Goal forall (C: Cat) A (f: C A A), idmap ∘ f ∘ (idmap ∘ f) ∘ f ≡ f ∘ (A ∘ f) ∘ (idmap ∘ f).
  intros. normalise. reflexivity.
  Restart.
  intros. by cat. 
  Restart.
  intros. rewrite cats'/=. reflexivity. 
Qed.
