(** * pullbacks *)

Require Import cat morphisms span cospan.
Require Import arewrite.

Local Open Scope cat_scope.

Definition square (𝐂: PreCat) (a b x y: ob 𝐂) (p: hom x a) (q: hom x b) (i: hom a y) (j: hom b y) :=
  p \; i ≡ q \; j.
Arguments square {_} [_ _ _ _] _ _ _ _/.

Lemma squareC 𝐂 a b x y f g p q: @square 𝐂 a b x y f g p q -> square g f q p.
Proof. exact: eqv_sym. Qed.

#[primitive] HB.mixin Record IsSquareAbove (𝐂: PreCat) (a b y: ob 𝐂) (f: a ~> y) (g: b ~> y) x of SPAN 𝐂 a b x :=
  {#[canonical=no]squareAbove: @square 𝐂 a b x y pi1 pi2 f g}.
#[short(type=SquareAbove)]
HB.structure Definition SQUAREABOVE 𝐂 a b y f g := {x of IsSquareAbove 𝐂 a b y f g x&}. 
HB.instance Definition _ (𝐂: PreCat) a b y f g :=
  QUIVER.copy (@SquareAbove 𝐂 a b y f g) (kernel (fun x: SquareAbove _ _ => x: Span _ _)). 
HB.instance Definition _ (𝐂: Cat) a b y f g :=
  CAT.copy (@SquareAbove 𝐂 a b y f g) (kernel (fun x: SquareAbove _ _ => x: Span _ _)). 
Section s.
Context (𝐂: PreCat) (a b x y: ob 𝐂)
  (f: a ~> y) (g: b ~> y) (p: x ~> a) (q: x ~> b).
Definition square_above (H: square p q f g) := span p q.
HB.instance Definition _ H := SPAN.on (square_above H).
HB.instance Definition _ H := IsSquareAbove.Build 𝐂 a b y f g (square_above H) H.
Definition square_above_ H: SquareAbove f g := square_above H.
End s.

Section s.
Context (𝐂: Cat) (a b z: ob 𝐂) (f: a ~> z) (g: b ~> z).
Definition SquareAboveiso_sort (x y: SquareAbove f g) (i: x ≃ y): x ≃_𝐂 y :=
  iso_ (Spanhom_sort i¹) (Spanhom_sort i⁻¹) (isoP i). 

Definition squareaboveiso_ (x y: SquareAbove f g) (i: x ≃_𝐂 y) (H: spanhom pi1 pi2 pi1 pi2 i¹): x ≃ y :=
  @iso_ _ x y (exist _ i¹ H) (exist _ i⁻¹ (spanhom_inv H)) (isoP i).
End s.

Section s.
Context (𝐂: PreCat) (a b x y: ob 𝐂) (f: a ~> y) (g: b ~> y) (p: x ~> a) (q: x ~> b).
Definition is_pullback := 
  square p q f g ∧ 
    forall z (p': z ~> a) (q': z ~> b), square p' q' f g -> unique_sig (spanhom p' q' p q).

Lemma pullback_terminal (P: is_pullback): terminal (square_above_ P.1).
Proof. move=>z. exact: (P.2 z pi1 pi2 squareAbove). Defined.
Lemma terminal_pullback H: terminal (@square_above_ 𝐂 a b x y f g p q H) -> is_pullback.
Proof. move=>T. split=>//z p' q' H'; exact: (T (square_above_ H')). Defined.
End s.
Arguments is_pullback {_} [_ _ _ _] _ _ _ _/.

#[primitive] HB.mixin Record IsPullback 𝐂 a b y f g x of @SQUAREABOVE 𝐂 a b y f g x :=
  {#[canonical=no]pullbackP: @is_pullback 𝐂 a b x y f g pi1 pi2}.
#[short(type=Pullback)]
HB.structure Definition PULLBACK 𝐂 a b y f g := {x of IsPullback 𝐂 a b y f g x&}. 
Section s.
Context {𝐂: PreCat} (a b y: ob 𝐂) (f: a ~> y) (g: b ~> y).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Pullback f g) := IsTerminal.Build (SquareAbove f g) (x: SquareAbove _ _) (pullback_terminal pullbackP).
Definition pullback x p q (H: is_pullback (x:=x) f g p q) := square_above H.1.
HB.instance Definition _ x p q H := SQUAREABOVE.on (@pullback x p q H). 
HB.instance Definition _ x p q H := IsPullback.Build 𝐂 a b y f g (@pullback x p q H) H. 
Definition pullback_ x p q H: Pullback f g := @pullback x p q H.
End s.

Section s.
Context (𝐂: PreCat) (a b y: ob 𝐂) (f: a ~> y) (g: b ~> y).

Lemma pullbackC x p q: @is_pullback 𝐂 a b x y f g p q -> is_pullback g f q p.
Proof.
  move=>P.
  split. apply: squareC. exact: P.1.
  move=>z p' q' H. move: (P.2 z q' p' (squareC H)).
  apply: unique_sig_impl=>/=h.
  split; exact: swap_pair. 
Qed.

Definition PullbackC (x: Pullback f g): Pullback g f :=
  pullback (pullbackC (pullbackP (s:=x))).

End s.

Section s.
Context (𝐂: Cat).
Implicit Types a b c d: ob 𝐂.

Section s.
Variables (a b z: ob 𝐂) (f: a ~> z) (g: b ~> z) (x y: Pullback f g).
Definition PullbackU_SquareAbove: (x: SquareAbove _ _) ≃ (y: SquareAbove _ _) :=
  TerminalU _ _.
Definition PullbackU: x ≃ y :=
  SquareAboveiso_sort PullbackU_SquareAbove.
Lemma PullbackUH: @spanhom _ a b x y pi1 pi2 pi1 pi2 PullbackU¹.
Proof. exact: SpanH. Qed.
End s.

Lemma pullback_id1 a b (f: a ~> b): is_pullback b f f a.
Proof.
  split=>/=. cat.
  move=>x p q H. unshelve apply: mk_unique_sig. exact: q.
  split. rewrite -H. cat. cat. 
  move=>/=y [_ <-]. cat. 
Qed.

Definition Pullback_id1 a b (f: a ~> b): Pullback b f :=
  pullback (pullback_id1 f).

Lemma pullback_id2 a b (f: a ~> b): is_pullback f b a f.
Proof. apply pullbackC, pullback_id1. Qed.

Definition Pullback_id2 a b (f: a ~> b): Pullback f b := PullbackC (Pullback_id1 f).

End s.                                                

(** ** categories with all pullbacks *)
#[primitive] HB.mixin Record HasPullbacks 𝐂 of PRECAT 𝐂 := {
    #[canonical=no] pb: forall a b y: ob 𝐂, forall f: a~>y, forall g: b~>y, Pullback f g;
  }.

#[short(type="CatPb")]
HB.structure Definition CATPB := { 𝐂 of CAT 𝐂 & HasPullbacks 𝐂 }.
Arguments pb {_ _ _ _}.

Section s.
Context {𝐂: CatPb}.
Implicit Types a b c d x y: ob 𝐂.

Definition pb1 a b y (f: a ~> y) (g: b ~> y): pb f g ~> a := pi1 (s:=pb f g). 
Definition pb2 a b y (f: a ~> y) (g: b ~> y): pb f g ~> b := pi2 (s:=pb f g).
Arguments pb1 {_ _ _ _ _}, {_ _ _} _ _.
Arguments pb2 {_ _ _ _ _}, {_ _ _} _ _.

Definition pbP a b y (f: a ~> y) (g: b ~> y): is_pullback f g pb1 pb2 := pullbackP. 

End s.
