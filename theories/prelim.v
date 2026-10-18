
From PartialOrders Require Export setoid.
From Stdlib Require Import CMorphisms.

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

(* unused so far *)
Reserved Notation "a ⥲ b" (at level 99, b at level 200, format "a  ⥲  b").
Reserved Notation "a ⥲_ 𝐂 b" (at level 99, 𝐂 at level 0).

(** functors *)
Reserved Notation "F ≈> G" (at level 99, G at level 200, format "F  ≈>  G").

(** natural isomorphisms *)
Reserved Notation "F ≈ G" (at level 70).

(** composition *)
Reserved Notation "f \; g" (at level 60, right associativity). 
Reserved Notation "f \;_ 𝐂 g" (at level 60, 𝐂 at level 0).
Reserved Notation "f ;; g" (at level 60, right associativity, format "f  ;;  g").
Reserved Notation "f ∘ g" (at level 40, left associativity). 
Reserved Notation "f ∘_ 𝐂 g" (at level 40, 𝐂 at level 0).
Reserved Notation "f ∘∘ g" (at level 40, left associativity). 

(** inverse *)
Reserved Notation "f '⁻¹'" (at level 1, format "f '⁻¹'").
Reserved Notation "f '¹'" (at level 1, format "f '¹'").

(** product *)
Reserved Notation "f × g" (at level 30).

(** tensor (in monoidal categories) *)
Reserved Notation "X ⊗ Y" (at level 31, right associativity). (* objects *)
Reserved Notation "f · g" (at level 30, right associativity). (* morphisms *)
Reserved Notation "n ⊚ m" (at level 30, right associativity). (* natural transformations *)

(** opposite category *)
Reserved Notation "𝐂 ^op" (at level 1, format "𝐂 ^op").

(** unique existence of morphisms *)
Reserved Notation "Σ! x .. y , P" (at level 200, x binder, y binder, right associativity).

(** iff/and in Type *)
Notation "A ⇆ B" := (iffT A B) (at level 95, B at next level). 
Infix "∧" := prod (at level 80).

(** for temporarily admitting things *)
Axiom sorry: forall {A: Type}, A.
Ltac sorry := exact: sorry. 

(** tag for objects in categories *)
Definition ob (𝐂: Type) := 𝐂. 


(** * complements to the partial order library (TO be moved there) *)

Section s.
Context [A B: Setoid.type] (f: A -> B).
Definition injective := forall x y, f x ≡ f y -> x ≡ y.
Definition surjective := forall b, exists a, f a ≡ b.
Definition bijective := injective /\ surjective.
End s.

(** Unique existence *)

(* TODO: move to partialorders lib *)
Definition unique (X: Setoid.type) := X ∧ (forall x y: X, x ≡ y).
Coercion unique_elt X (x: unique X): X := x.1.
Definition unicity (X: Setoid.type) (U: unique X): forall x y: X, x ≡ y := U.2.
Lemma mk_unique (X: Setoid.type) (x: X) (H: forall y, x ≡ y): unique X.
Proof. split. exact: x. abstract (move=>y z; by rewrite -(H y)). Defined.

Lemma unique_impl (X Y: Setoid.type) (f: X -> Y) (g: Y -> X) (I: injective g):
  unique X -> unique Y.
Proof.
  move=>x. split. exact: (f x).
  move=>y y'. apply: I. exact: unicity. 
Defined.

Section s.
Variables (X: Setoid.type) (P: X -> Prop). 
Definition unique_sig := unique (sig P).
Coercion unique_sig_elt (x: unique_sig): X := sval x.1.
Lemma unique_sigP (x: unique_sig): P x. Proof. exact: proj2_sig. Defined.
Definition unicity_sig (U: unique_sig) x y: P x -> P y -> x ≡ y.
Proof. move=>p q. exact: (unicity U (exist _ x p) (exist _ y q)). Qed.
Lemma mk_unique_sig (x: X) (p: P x) (H: forall y, P y -> x ≡ y): unique_sig.
Proof. unshelve apply: mk_unique. by exists x. abstract (move=>[y q]; exact: H y q). Defined.
End s.

Lemma unique_sig_impl (X: Setoid.type) P Q (H: forall x: X, P x <-> Q x): unique_sig P -> unique_sig Q.
Proof.
  unshelve apply: unique_impl. 
  1,2: move=>x; exists (sval x); by apply H, proj2_sig.
  by move=>[??][??]. 
Defined.

Lemma unique_sig_eqv (X: Setoid.type) P Q (H: forall x: X, P x <-> Q x): unique_sig P ⇆ unique_sig Q.
Proof. split; apply: unique_sig_impl=>//. firstorder. Defined.

Notation "Σ! x .. y , P" := (unique_sig (fun x => .. (unique_sig (fun y => P)) ..)). 
