(** testing rewriting and reflexivity modulo associativity and split epi / split mono / isos
    this file was originally written by Kazuhiko Sazkaguchi, late 2025 - early 2026,
    in the context of the graph-rewriting library we developped with Samuel Arsac
 *)

Require Import cat morphisms functor airewrite.

Local Open Scope cat_scope.

Section s.
Context (C : Cat).
Variables a b c d e: ob C. 

Goal forall (f : SplitMono a a), f \; f⁻¹ ≡ idmap.
Proof.
  move=>f. aireflexivity. 
Qed.

Goal forall (f : SplitEpi a a), f⁻¹ \; f ≡ idmap.
Proof.
  move=>f. aireflexivity. 
Qed.

Goal forall (f : SplitMono a a) (g fg : a ~> a), f ∘ g ≡ fg -> g ≡ f⁻¹ ∘ fg.
Proof.
move=> f g fg H.
(* The default pattern [comp _ _] cannot select the right subterm [g]. *)
Fail airewrite H.
(* But, it works if we explicitly select [g]. *)
airewrite [g]H.
done.
Qed.

Goal forall (g : SplitMono a a) (f fg : a ~> a), f ∘ g⁻¹ ≡ fg -> f ≡ fg ∘ g.
Proof.
move=> g f fg H.
Fail airewrite H. (* same here *)
airewrite [f]H.
done.
Qed.

Goal forall (f : SplitEpi a a) (g fg : a ~> a), f⁻¹ ∘ g ≡ fg -> g ≡ f ∘ fg.
Proof.
move=> f g fg H.
Fail airewrite H. (* same here *)
airewrite [g]H.
done.
Qed.

Goal forall (g : SplitEpi a a) (f fg : a ~> a), f ∘ g ≡ fg -> f ≡ fg ∘ g⁻¹.
Proof.
move=> g f fg H.
Fail airewrite H. (* same here *)
airewrite [f]H.
done.
Qed.

End s.

Print Assumptions all.
