From Stdlib Require Import List.
From mathcomp Require Import ssreflect.

Definition arity X := list X.
Infix "++" := app. 
Infix "::" := cons. 

Section s.
Context {X: Type}.
Implicit Types A B C D: X.
Implicit Types a b c d Γ Δ Θ: arity X.

(** reified arities: lists of (abstract) objects and abstract arities *)
Definition rarity := list (arity X).
Implicit Types h k l q: rarity.
Bind Scope list_scope with rarity.

(** transparent versions of [app_assoc] and [app_nil_r] *)
Fixpoint aappU Γ: Γ ++ nil = Γ.
  by case: Γ=>//=*; apply: f_equal.
Defined. (* defined so that [find_eq_arity] eventually produces [eq_refl] *)
Fixpoint aappA Γ Δ Θ: (Γ ++ Δ) ++ Θ = Γ ++ (Δ ++ Θ).
  by case: Γ=>//=*; apply: f_equal.
Defined. (* defined so that [find_eq_arity] eventually produces [eq_refl] *)

(** flattening a reified arity into a mere arity *)
Fixpoint flatten l :=
  match l with
  | nil => nil
  | cons Γ q => Γ ++ flatten q
  end.

Fixpoint flatten_app h k: flatten (h++k) = flatten h ++ flatten k.
Proof.
  destruct h. reflexivity. cbn.
  rewrite aappA. f_equal. exact: flatten_app.
Defined. (* defined so that [find_eq_arity] eventually produces [eq_refl] *)

Structure reified_ar_ := reify_ar_ {
    rar_':> arity X;
    #[canonical=no] rar_: rarity;
    #[canonical=no] rar_E: flatten rar_ = rar_';
  }.
Implicit Types x y: reified_ar_.
Arguments reify_ar_: clear implicits.


(* all instances below must be defined so that [find_eq_arity] eventually produces [eq_refl] *)
Import List.ListNotations.
Canonical rar_nil_ :=
  reify_ar_ [] [] eq_refl.
Canonical rar_cons_ A x :=
  reify_ar_ (A :: rar_' x) ([A] :: rar_ x) (f_equal (cons A) (rar_E x)).
Program Canonical rar_app_ x y :=
  reify_ar_ (rar_' x ++ rar_' y) (rar_ x ++ rar_ y) _.
Next Obligation. intros. by rewrite flatten_app 2!rar_E. Defined. (* idem *)
Canonical rar_var_ Γ :=
  reify_ar_ Γ [Γ] (aappU _). 

Lemma eq_arity [x y: reified_ar_]: flatten (rar_ x) = flatten (rar_ y) -> rar_' x = rar_' y.
Proof. by rewrite 2!rar_E. Defined. (* idem *)

End s.
Arguments rarity: clear implicits.
Arguments eq_arity [_ _ _]&_. 
Notation find_eq_arity := (eq_arity eq_refl).

Section tests.

Context {X: Type}.
Variables A B C: X.
Variables Γ Δ Θ: arity X.

Check find_eq_arity: Γ++(Δ++Θ)++(Γ++Δ)++Θ = (Γ++Δ)++(Θ++Γ)++(Δ++Θ). 
Check find_eq_arity: Γ++(Δ++Θ)++(A::Δ)++Θ = (Γ++Δ)++(Θ++A::nil)++(Δ++Θ).

End tests.
