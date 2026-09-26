(** testing rewriting and reflexivity modulo associativity and identities
    this file was originally written by Kazuhiko Sazkaguchi, late 2025 - early 2026,
    in the context of the graph-rewriting library we developped with Samuel Arsac
 *)

Require Import cat functor arewrite.

Local Open Scope cat_scope.

Section s.
Context (C : Cat).
Variables a b c d e: ob C. 


Goal forall (f : a ~> a), f \; f \; idmap \; f ≡ f \; idmap \; f \; f.
Proof.
  move=>f. areflexivity. 
Qed.

Goal forall (f f' : a ~> b) (g g' : b ~> c) (h : c ~> d),
    g ∘ f ≡ g' ∘ f' -> h ∘ g ∘ f ≡ h ∘ g' ∘ f'.
Proof.
move=> f f' g g' h H.
Fail rewrite H.
Succeed rewrite -compoA H.
Succeed arewrite H.
arewrite [X in eqv X _]H.
areflexivity.
Qed.

Goal forall (f f' : a ~> b) (g g' : b ~> c) (h : c ~> d) (i: d ~> a),
    g ∘ f ≡ g' ∘ f' -> h ∘ g ∘ f ∘ i ≡ h ∘ g' ∘ f' ∘ i.
Proof.
move=> f f' g g' h i H.
Fail rewrite H.
Fail rewrite -compoA H.
Succeed arewrite H.
arewrite [X in eqv X _]H.
areflexivity.
Qed.

Goal forall (f: a ~> c) (g: b ≃ c) (h : c ~> d),
    h ∘ g¹ ∘ g⁻¹ ∘ f ≡ h ∘ f.
Proof.
move=> f g h.
arewrite invKl.                  (* nice! *)
areflexivity.
Qed.

Goal forall (F G: Functor C C) (l: F ~> G) (f: a ~> a) (g: G a ~> G a) (h: F a ~> F a),
    g ∘ l a ∘ (Fhom F f) ∘ h ≡ g ∘ (Fhom G f) ∘ l a ∘ h.
Proof.
move=>F G l f g h.
arewrite natural.                  (* nice! *)
areflexivity.
Qed.

Goal forall (f g h i: a ~> a),
    (forall x: a~>a, x ∘ x ≡ idmap) -> g ∘ f ∘ g ∘ g ∘ g ∘ f ≡ idmap.
Proof.
  move=> f g h i H.
  arewrite (H g). 
  arewrite (H (g∘f)).
  reflexivity.
  Restart.
  move=> f g h i H.
  arewrite H.    (* instantiates with [idmap], which is not optimal *)
Abort.

Goal forall (f g h i: a ~> a),
    (forall x, f ∘ x ∘ h ≡ idmap) -> g ∘ f ∘ g ∘ g ∘ h ∘ g ≡ g ∘ g.
Proof.
move=> f g h i H.
Fail rewrite H.
arewrite H.
areflexivity.
Qed.

Goal forall (f g h i: a ~> a),
    (forall x, f ∘ x ∘ h ≡ idmap) -> g ∘ f ∘ g ∘ h ∘ g ≡ g ∘ g.
Proof.
move=> f g h i H.
Fail rewrite H.
Succeed arewrite (H g); areflexivity.
arewrite H.
areflexivity.
Qed.


Goal forall (f f' : a ~> b) (g g' : b ~> c) (h : c ~> d) (i: d ~> a),
    (True -> g ∘ f ≡ g' ∘ f') -> h ∘ g ∘ f ∘ i ≡ h ∘ g' ∘ f' ∘ i.
Proof.
move=> f f' g g' h i H.
arewrite H. done. areflexivity. 
Qed.


Goal forall (f g h i: a ~> a) P,
    (forall x, P x -> f ∘ x ∘ h ≡ idmap) -> g ∘ f ∘ g ∘ h ∘ g ≡ g ∘ g.
Proof.
move=> f g h i P H.
arewrite (H g).
2: areflexivity.
Abort.

End s.

Print Assumptions all.
