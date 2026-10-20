(** * pushouts *)

Require Export pullback.
Require Import arewrite.

Local Open Scope cat_scope.

#[primitive] HB.mixin Record IsSquareBelow (𝐂: PreCat) (a b x: ob 𝐂) (f: x ~> a) (g: x ~> b) y of COSPAN 𝐂 a b y :=
  {#[canonical=no]squareBelow: @square 𝐂 a b x y f g in1 in2}.
#[short(type=SquareBelow)]
HB.structure Definition SQUAREBELOW 𝐂 a b x f g := {y of IsSquareBelow 𝐂 a b x f g y&}. 
HB.instance Definition _ (𝐂: PreCat) a b x f g :=
  QUIVER.copy (@SquareBelow 𝐂 a b x f g) (kernel (fun x: SquareBelow _ _ => x: Cospan _ _)). 
HB.instance Definition _ (𝐂: Cat) a b x f g :=
  CAT.copy (@SquareBelow 𝐂 a b x f g) (kernel (fun x: SquareBelow _ _ => x: Cospan _ _)). 
Section s.
Context (𝐂: PreCat) (a b x y: ob 𝐂)
  (f: x ~> a) (g: x ~> b) (i: a ~> y) (j: b ~> y).
Definition square_below (H: square f g i j) := cospan i j.
HB.instance Definition _ H := COSPAN.on (square_below H).
HB.instance Definition _ H := IsSquareBelow.Build 𝐂 a b x f g (square_below H) H.
Definition square_below_ H: SquareBelow f g := square_below H.
End s.

Section s.
Context (C: PreCat) (a b: ob C).
HB.instance Definition _ x f g (y: @SquareAbove C a b x f g) :=
  IsSquareBelow.Build (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g) (obop (y: ob C)) squareAbove.
HB.instance Definition _ x f g (y: @SquareAbove (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g)) :=
  IsSquareBelow.Build C a b x f g (obop' (y: ob C)) (squareAbove (s:=y)).
HB.instance Definition _ x f g (y: @SquareBelow C a b x f g) :=
  IsSquareAbove.Build (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g) (obop (y: ob C)) squareBelow.
HB.instance Definition _ x f g (y: @SquareBelow (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g)) :=
  IsSquareAbove.Build C a b x f g (obop' (y: ob C)) (squareBelow (s:=y)).
End s.


Section s.
Context (𝐂: Cat) (a b z: ob 𝐂) (f: z ~> a) (g: z ~> b).
Definition SquareBelowiso_sort (x y: SquareBelow f g) (i: x ≃ y): x ≃_𝐂 y :=
  iso_ (Cospanhom_sort i¹) (Cospanhom_sort i⁻¹) (invKl i) (invKr i). 

Definition squarebelowiso_ (x y: SquareBelow f g) (i: x ≃_𝐂 y) (H: cospanhom in1 in2 in1 in2 i¹): x ≃ y :=
  @iso_ _ x y (exist _ i¹ H) (exist _ i⁻¹ (cospanhom_inv H)) (invKl i) (invKr i).
End s.

Section s.
Context (𝐂: PreCat) (a b x y: ob 𝐂) (f: x ~> a) (g: x ~> b) (i: a ~> y) (j: b ~> y).
Definition is_pushout := 
  square f g i j ∧ 
    forall z (i': a ~> z) (j': b ~> z), square f g i' j' -> unique_sig (cospanhom i j i' j').

Lemma pushout_initial (P: is_pushout): initial (square_below_ P.1).
Proof. move=>z. exact: (P.2 z in1 in2 squareBelow). Defined.
Lemma initial_pushout H: initial (@square_below_ 𝐂 a b x y f g i j H) -> is_pushout.
Proof. move=>T. split=>//z i' j' H'; exact: (T (square_below_ H')). Defined.
End s.
Arguments is_pushout {_} [_ _ _ _] _ _ _ _/.

#[primitive] HB.mixin Record IsPushout 𝐂 a b x f g y of @SQUAREBELOW 𝐂 a b x f g y :=
  {#[canonical=no]pushoutP: @is_pushout 𝐂 a b x y f g in1 in2}.
#[short(type=Pushout)]
HB.structure Definition PUSHOUT 𝐂 a b x f g := {y of IsPushout 𝐂 a b x f g y&}. 
Section s.
Context {𝐂: PreCat} (a b x: ob 𝐂) (f: x ~> a) (g: x ~> b).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (y: Pushout f g) := IsInitial.Build (SquareBelow f g) (y: SquareBelow _ _) (pushout_initial pushoutP).
Definition pushout y i j (H: is_pushout (y:=y) f g i j) := square_below H.1.
HB.instance Definition _ y i j H := SQUAREBELOW.on (@pushout y i j H). 
HB.instance Definition _ y i j H := IsPushout.Build 𝐂 a b x f g (@pushout y i j H) H. 
Definition pushout_ y i j H: Pushout f g := @pushout y i j H.
End s.

Section s.
Context (C: PreCat) (a b: ob C).
HB.instance Definition _ x f g (y: @Pullback C a b x f g) :=
  IsPushout.Build (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g) (obop (y: ob C)) ((* is_pullback_op *) pullbackP).
HB.instance Definition _ x f g (y: @Pullback (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g)) :=
  IsPushout.Build C a b x f g (obop' (y: ob C)) (pullbackP (s:=y)).
HB.instance Definition _ x f g (y: @Pushout C a b x f g) :=
  IsPullback.Build (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g) (obop (y: ob C)) ((* is_pushout_op *) pushoutP).
HB.instance Definition _ x f g (y: @Pushout (op C) (obop a) (obop b) (obop x) (morphop f) (morphop g)) :=
  IsPullback.Build C a b x f g (obop' (y: ob C)) (pushoutP (s:=y)).
End s.


Section s.
Context (𝐂: PreCat) (a b x: ob 𝐂) (f: x ~> a) (g: x ~> b).

Lemma pushoutC y i j: @is_pushout 𝐂 a b x y f g i j -> is_pushout g f j i.
Proof. exact: (@pullbackC 𝐂^op). Qed.

(* TOTHINK: which definition should we prefer? *)
Definition PushoutC (y: Pushout f g): Pushout g f :=
  obop' (PullbackC (obop y)). 
Definition PushoutC' (y: Pushout f g): Pushout g f :=
  pushout (pushoutC (pushoutP (s:=y))).

End s.

Section s.
Context (𝐂: Cat).
Implicit Types a b c d: ob 𝐂.

Section s.
Variables (a b z: ob 𝐂) (f: z ~> a) (g: z ~> b) (x y: Pushout f g).
Definition PushoutU_SquareBelow: (x: SquareBelow _ _) ≃ (y: SquareBelow _ _) :=
  InitialU _ _.
Definition PushoutU: x ≃ y :=
  SquareBelowiso_sort PushoutU_SquareBelow.
Lemma PushoutUH: @cospanhom _ a b x y in1 in2 in1 in2 PushoutU¹.
Proof. exact: CospanH. Qed.
End s.

Lemma pushout_id1 a b (f: a ~> b): is_pushout a f f b.
Proof. exact: (pullback_id1 (morphop f)). Qed.

Definition Pushout_id1 a b (f: a ~> b): Pushout a f :=
  obop' (Pullback_id1 (morphop f)).
Definition Pushout_id1' a b (f: a ~> b): Pushout a f :=
  pushout (pushout_id1 f).

Lemma pushout_id2 a b (f: a ~> b): is_pushout f a b f.
Proof. exact: (pullback_id2 (morphop f)). Qed.

Definition Pushout_id2 a b (f: a ~> b): Pushout f a :=
  obop' (Pullback_id2 (morphop f)).

End s.                                                

(** ** categories with all pushouts *)
#[primitive] HB.mixin Record HasPushouts 𝐂 of PRECAT 𝐂 := {
    #[canonical=no] po: forall a b x: ob 𝐂, forall f: x~>a, forall g: x~>b, Pushout f g;
  }.

#[short(type="CatPo")]
HB.structure Definition CATPO := { 𝐂 of CAT 𝐂 & HasPushouts 𝐂 }.
Arguments po {_ _ _ _}.

HB.instance Definition _ (𝐂: CatPb) :=
  HasPushouts.Build (𝐂^op) (fun _ _ _ f g => obop (pb (morphop f) (morphop g))).
HB.instance Definition _ (𝐂: CatPo) :=
  HasPullbacks.Build (𝐂^op) (fun _ _ _ f g => obop (po (morphop f) (morphop g))).

Section s.
Context {𝐂: CatPo}.
Implicit Types a b c d x y: ob 𝐂.

Definition po1 a b x (f: x ~> a) (g: x ~> b): a ~> po f g := in1 (s:=po f g). 
Definition po2 a b x (f: x ~> a) (g: x ~> b): b ~> po f g := in2 (s:=po f g).
Arguments po1 {_ _ _ _ _}, {_ _ _} _ _.
Arguments po2 {_ _ _ _ _}, {_ _ _} _ _.

Definition poP a b x (f: x ~> a) (g: x ~> b): is_pushout f g po1 po2 := pushoutP. 

End s.
