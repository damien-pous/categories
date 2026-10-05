
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
