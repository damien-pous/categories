Require Export monoidal_def.
Require Import monoidal_mclane monoidal_gmclane monoidal_tactic.

Local Open Scope cat_scope.

Definition box {X} (x: X) := x.

Lemma box_lr {𝐂: Quiver} {A B: 𝐂} (f g: A ~> B) :
  f ≡ g -> box f ≡ g.
Proof. done. Qed.

Lemma box_rl {𝐂: Cat} {A' A B B': 𝐂} (i: A'≃A) (j: B≃B') f g:
  f ≡ cast' i j g -> box g ≡ cast' (blocked_inv i) (blocked_inv j) f.
Proof. move=>->. symmetry. exact/cast_switch. Qed.


Ltac mcat := by (rewrite /box; M.mcat).
Ltac mcat_debug := rewrite /box; M.mcat'.

Ltac McLane := gMcLane.
#[export] Hint Extern 0 (Bridge _ _) => find_gmclane: typeclass_instances.
#[export] Hint Extern 0 (auto_eqv _ _) => gMcLane: typeclass_instances.

Tactic Notation "transitivity'" constr(g) :=
  lazymatch goal with
  | |- _ ≡[hom ?A ?B] cast _ => apply: (eqv_trans_cast' g mcl mcl)=>/= 
  | |- _ ≡[hom ?A ?B] _ => apply: (eqv_trans_cast g mcl mcl)=>/= 
  | _ => fail "not an equality between morphisms"
  end.

Tactic Notation "brewrite" "-" constr(H) := rewrite (box_rl H).
Tactic Notation "brewrite" constr(H) := rewrite (box_lr H).

Module Notations.
Export SEEOBJ.
Notation "x ≡' y" := (x ≡ acast y) (at level 70, only parsing): cat_scope.
Notation "x ≡' y" := (x ≡ cast y) (at level 70, only printing): cat_scope.
Notation "f  \; g" := (comp f g): cat_scope. 
Notation "f  ;; g" := (bcomp f g mcl) (at level 39, right associativity, only parsing): cat_scope. 
Notation "f  ;; g" := (bcomp f g _) (at level 39, right associativity, only printing): cat_scope. 
Notation "f" := (cast f) (at level 1, only printing): cat_scope.
Notation "[ f ]" := (box f): cat_scope. 
End Notations. 

Module NiceNotations.
Export Notations.
Notation "f  ; g" := (comp f g) (at level 39, right associativity): cat_scope. 
Tactic Notation "transitivity" constr(g) := transitivity' g.
Tactic Notation "rewrite" "-" constr(H) := brewrite -H.
Tactic Notation "rewrite" constr(H) := brewrite H.
End NiceNotations.


Section more_theory.

Context {𝐂: MonoidalCat}.
Implicit Types A B C D: 𝐂.

Lemma tensor_comm A B (f: A ~> unit) (g: unit ~> B): f·g ≡ acast (g·f).
Proof.
  rewrite tensor_lr tensorUl tensorUr.
  rewrite tensor_rl tensorUl tensorUr.
  rewrite cast_comp 2!castI. McLane. 
Qed.

Lemma tensor_comm' (f g: unit ~>_𝐂 unit): f·g ≡ g·f.
Proof.
  rewrite tensor_lr tensorUl tensorUr.
  rewrite tensor_rl tensorUl tensorUr.
  McLane. 
Qed.

End more_theory.
