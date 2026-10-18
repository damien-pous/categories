(** rewriting and reflexivity modulo associativity
    this file was originally written by Kazuhiko Sakaguchi, late 2025 - early 2026,
    in the context of the graph-rewriting library we developped with Samuel Arsac
    adapted by Damien Pous to deal with the new way categorical structures are defined
 *)

From elpi Require Import elpi.
From mathcomp Require Import ssrmatching ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import cat.
From Categories.elpi Extra Dependency "common.elpi" as common.
From Categories.elpi Extra Dependency "areflexivity.elpi" as areflexivity.
From Categories.elpi Extra Dependency "arewrite.elpi" as arewrite.

Local Open Scope cat_scope.

Module Import Internals.
Section s.

Context (C : BarePreCat).
Implicit Type (a b c d : ob C).

(* syntax trees for reasoning modulo associativity *)
Inductive aexpr : ob C -> ob C -> Type :=
  | ae_var a b (q : a ~> b) : aexpr a b
  | ae_id a : aexpr a a
  | ae_comp a b c : aexpr a b -> aexpr b c -> aexpr a c.

Definition ae_cons a b c (q : a ~> b) : aexpr b c -> aexpr a c :=
  ae_comp (ae_var q).

Fixpoint ae_eval a b (e : aexpr a b) : a ~> b :=
  match e with
  | ae_var q => q
  | ae_id a => idmap
  | ae_comp e1 e2 => ae_eval e1 \; ae_eval e2
  end.

Fixpoint ae_norm a b c (e : aexpr a b) : (b ~> c) -> (a ~> c) :=
  match e with
  | ae_var q => fun acc => q \; acc
  | ae_id _ => fun acc => acc
  | ae_comp e1 e2 => fun acc => ae_norm e1 (ae_norm e2 acc)
  end.

End s.
Section s.

Context (C : Cat).
Implicit Type (a b c d : ob C).

Lemma ae_correct a b c (e : aexpr a b) (acc : b ~> c) :
  eqv (ae_eval e \; acc) (ae_norm e acc).
Proof.
elim: {a b}e c acc => //=; first by move=> a b acc; rewrite comp1o.
by move=> a b c e1 IHe1 e2 IHe2 d acc; rewrite compoA IHe2 IHe1.
Qed.

(* lemmas for areflexivity *)
Lemma areflexivity_correct a b (e1 e2 : aexpr a b) :
  ae_norm e1 idmap = ae_norm e2 idmap -> eqv (ae_eval e1) (ae_eval e2).
Proof. by move/eq_eqv; rewrite -!ae_correct !compo1. Qed.

(* lemmas for arewrite *)
Lemma add_prepost a b c d (pre : a ~> b) (p q : b ~> c) (post : c ~> d) :
  eqv p q -> eqv (pre \; p \; post) (pre \; q \; post).
Proof. by move=> ->. Qed.

Lemma arewrite_correct a b (e lhs : aexpr a b) (rhs : a ~> b) :
  ae_norm e idmap = ae_norm lhs idmap ->
  eqv (ae_eval lhs) rhs -> eqv (ae_eval e) rhs.
Proof. by move=> /eq_eqv; rewrite -!ae_correct !compo1 => ->. Qed.

End s.

End Internals.


Local Abbreviation barequiver_of_cat := cat_CAT__to__cat_BAREQUIVER.
Local Abbreviation bareprecat_of_cat := cat_CAT__to__cat_BAREPRECAT.

(* Elpi code for areflexivity *)

Elpi Tactic areflexivity.
Elpi Accumulate File common.
Elpi Accumulate File areflexivity.

Ltac areflexivity := elpi areflexivity.

Section test.
Context (C : Cat).
Variables a b: ob C.
Goal forall (f : a ~> a), f \; f \; idmap \; f ≡ f \; idmap \; f \; f.
Proof.
  move=>f. areflexivity.
Qed.
End test.


(* Elpi code for arewrite *)

Elpi Tactic arewrite_proofgen.
Elpi Accumulate File common.
Elpi Accumulate File arewrite.

Tactic Notation "arewrite" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi arewrite_proofgen "lr" (Selected) (proof));
    rewrite 1?comp1o 1?compo1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "arewrite" "-" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi arewrite_proofgen "rl" (Selected) (proof));
    rewrite 1?comp1o 1?compo1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "arewrite" uconstr(proof) := arewrite [comp _ _]proof.

Tactic Notation "arewrite" "-" uconstr(proof) := arewrite -[comp _ _]proof.

Section test.
Context (C : Cat).
Variables a b c d: ob C.
Goal forall (f f' : a ~> b) (g g' : b ~> c) (h : c ~> d),
    g ∘ f ≡ g' ∘ f' -> h ∘ g ∘ f ≡ h ∘ g' ∘ f'.
Proof.
move=> f f' g g' h H.
arewrite H.
areflexivity.
Qed.
End test.

