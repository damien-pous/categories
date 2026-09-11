(** rewriting and reflexivity modulo associativity and split epi / split mono / isos
    this file was originally written by Kazuhiko Sazkaguchi, late 2025 - early 2026,
    in the context of the graph-rewriting library we developped with Samuel Arsac
 *)

From elpi Require Import elpi.
From mathcomp Require Import ssrmatching ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import cat morphisms.
Require arewrite.
From Categories.elpi Extra Dependency "common.elpi" as common.
From Categories.elpi Extra Dependency "inv_common.elpi" as inv_common.
From Categories.elpi Extra Dependency "aireflexivity.elpi" as aireflexivity.
From Categories.elpi Extra Dependency "airewrite.elpi" as airewrite.

Local Open Scope cat_scope.

Module Import Internals.
Import arewrite.Internals.
Section syntax.

Context (C : PreCat).
Implicit Type (a b c : C).

(* syntax trees for reasoning modulo cancellation (of mono, epi, and iso) *)
Inductive iexpr : C -> Type :=
  | can_mono (a b : C) : SplitMono a b -> list (iexpr b) -> iexpr a.

Fixpoint ie_eval a b (e : iexpr a) : (a ~> b) -> (a ~> b) :=
  let: can_mono mono es := e in
  fun acc => mono \; foldr (@ie_eval _ _) (inv mono \; acc) es.

Inductive cexpr : C -> C -> Type :=
  | ce_id (a : C) : cexpr a a
  | ce_icons (f : bool) (a b : C) : iexpr a -> cexpr a b -> cexpr a b
  | ce_cons (a b c : C) : (a ~> b) -> cexpr b c -> cexpr a c.

Fixpoint ce_eval (f : bool) a b c (e : cexpr a b) : (b ~> c) -> (a ~> c) :=
  match e with
  | ce_id _ => id
  | ce_icons f' e1 e2 => fun acc =>
    (if eqb f f' then ie_eval e1 else id) (ce_eval f e2 acc)
  | ce_cons m e => fun acc => m \; ce_eval f e acc
  end.

End syntax.

Section correct.

Context (C : Cat).
Implicit Type (a b c d : C).

Lemma ie_correct a b (e : iexpr a) (acc : a ~> b) : eqv (ie_eval e acc) acc.
Proof.
move: a b e acc; fix IHe 3 => _ c [] a b m /=; elim => [|e es IHes] acc /=.
  by rewrite -compoA invKr comp1o.
by rewrite IHe IHes.
Qed.

Lemma ce_correct a b c (e : cexpr a b) (acc : b ~> c) :
  eqv (ce_eval false e acc) (ce_eval true e acc).
Proof.
elim: e acc => //= [f {}a {}b e1 e2 IHe2|{}a a' {}b m e IHe] acc.
  by case: f; rewrite /= ie_correct.
by rewrite IHe.
Qed.

(* lemmas for arewrite *)
Definition add_prepost := arewrite.Internals.add_prepost.

(* lemmas for aireflexivity *)
Lemma aireflexivity_correct a b (e1 e2 : aexpr a b) (ce : cexpr a b) :
  ae_norm e1 idmap = ce_eval false ce idmap ->
  ce_eval true ce idmap = ae_norm e2 idmap ->
  eqv (ae_eval e1) (ae_eval e2).
Proof.
by move=> /eq_eqv + /eq_eqv; rewrite -!ae_correct ce_correct !compo1 => -> ->.
Qed.

(* lemmas for airewrite *)
Lemma airewrite_correct
    a b (e lhs : aexpr a b) (rhs : a ~> b) (ce : cexpr a b) :
  ae_norm e idmap = ce_eval false ce idmap ->
  ce_eval true ce idmap = ae_norm lhs idmap ->
  eqv (ae_eval lhs) rhs -> eqv (ae_eval e) rhs.
Proof.
by move=> /eq_eqv + /eq_eqv; rewrite -!ae_correct ce_correct !compo1 => -> ->.
Qed.

End correct.

End Internals.

Local Notation quiver_of_precat := cat_precat__to__cat_quiver.
Local Notation quiver_of_cat := cat_cat__to__cat_quiver.

Local Notation inverse_of_mono C a b mono :=
  (@inv C a b
     (@morphisms_splitmono__to__morphisms_invertible C a b mono)).
Local Notation inverse_of_epi C a b epi :=
  (@inv C a b
     (@morphisms_splitepi__to__morphisms_invertible C a b epi)).
(* Local Notation epi_of_mono C a b mono := *)
(*   (@morphisms_inv__canonical__morphisms_splitepi C a b mono). *)
Local Notation mono_of_epi C a b epi :=
  (@morphisms_inv__canonical__morphisms_splitmono C a b epi).


(* Elpi code for aireflexivity *)

Elpi Tactic aireflexivity.
Elpi Accumulate File common.
Elpi Accumulate File inv_common.
Elpi Accumulate File aireflexivity.

(* Elpi code for airewrite *)

Elpi Tactic airewrite_proofgen.
Elpi Accumulate File common.
Elpi Accumulate File inv_common.
Elpi Accumulate File airewrite.

(*********************)
(* Exporting tactics *)
(*********************)

Ltac aireflexivity := elpi aireflexivity.

(* airewrite *)

Tactic Notation "airewrite" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi airewrite_proofgen "lr" (Selected) (proof));
    rewrite 1?comp1o 1?compo1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "airewrite" "-" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi airewrite_proofgen "rl" (Selected) (proof));
    rewrite 1?comp1o 1?compo1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "airewrite" uconstr(proof) := airewrite [comp _ _]proof.

Tactic Notation "airewrite" "-" uconstr(proof) := airewrite -[comp _ _]proof.
