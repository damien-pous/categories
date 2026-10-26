(** * characterisation of pullbacks as limits *)

Require Import cat morphisms span pullback limit.
Require Import shape functor adjunction.

Open Scope cat_scope.

(** ** representation of squares above a cospan as cones over the copsan quiver *)

Section s.
Context {𝐂: Cat}.

Abbreviation Shape := shape.cospan.
Abbreviation Diagram := (Diagram Shape 𝐂).

Section s.
Variables (a b y: ob 𝐂) (f: a ~> y) (g: b ~> y).

Definition diagram: Diagram.
  exists (fun c: ob Shape => match c with shape.L => a | shape.C => y | shape.R => b end).
  by split; split=>??[]. 
Defined.

Abbreviation Cone := (cone diagram).
Abbreviation Square := (SquareAbove f g).

Definition Square_Cone (x: Square): Cone.
  exists (SQUAREABOVE.sort x). 
  exists (fun c: ob Shape => match c return SQUAREABOVE.sort x ~> diagram c with
                     | shape.L => pi1
                     | shape.C => pi2 \; g (* ≡ pi1 ; f *)
                     | shape.R => pi2
                     end).
  move=>??[]//. exact/squareAbove. 
Defined.

Program Definition Cone_Square (c: Cone): Square :=
  square_above_ (p:=cone_mor c shape.L) (q:=cone_mor c shape.R) _.
Next Obligation.
  move=>C/=. by rewrite (coneP C shape.cl) (coneP C shape.cr). 
Qed.

Lemma _Square_Cone_functor: IsFunctor _ _ Square_Cone.
Proof.
  unshelve eexists.
  - move=>X Y h. exists (Spanhom_sort h).
    abstract by case; cbn; rewrite -?compoA (SpanH h). 
  - by move=>X Y h h'.
  - by move=>X.
  - by move=>X Y Z h h'.
Defined.
HB.instance Definition _ := _Square_Cone_functor. 

Lemma _Cone_Square_functor: IsFunctor _ _ Cone_Square.
Proof.
  unshelve eexists.
  - move=>X Y h. exists (conehom_sort h).
    exact: (conehomP h shape.L, conehomP h shape.R).
  - by move=>X Y h h'.
  - by move=>X.
  - by move=>X Y Z h h'.
Defined.
HB.instance Definition _ := _Cone_Square_functor. 

Program Definition Square_Cone_adj: adjunction Square_Cone Cone_Square := Adj.mk _ _ _ _.
Next Obligation.
  unshelve eexists. exact: (fun c => idmap c).
  abstract by (split;split=>X Y h; cbn; cat).
Defined.
Next Obligation.
  unshelve eexists. cbn=>c.
  unshelve eexists. cbn. exact: idmap.
  abstract by case; cbn; rewrite !cats// (coneP c shape.cr).
  abstract by (split; split=>X Y h; cbn; rewrite !cats).
Defined.
Next Obligation. cbn=>c. cat. Qed.
Next Obligation. cbn=>c. cat. Qed.
Lemma Square_Cone_refl: Adj.is_reflection Square_Cone_adj.
  unshelve eexists. cbn=>c.
  unshelve eexists. cbn. exact: idmap.
  abstract by case; cbn; rewrite !cats// (coneP c shape.cr).
  abstract by split; cbn; cat. 
Defined.
Lemma Square_Cone_corefl: Adj.is_coreflection Square_Cone_adj.
  unshelve eexists. exact: (fun c => idmap c).
  abstract by split; cbn; cat. 
Defined.

HB.instance Definition _ := IsPreAdjointF.Build _ _ Square_Cone Cone_Square. 
HB.instance Definition _ := IsLeftAdjoint.Build _ _ Square_Cone Square_Cone_adj. 
HB.instance Definition _ := IsLeftReflection.Build _ _ Square_Cone Square_Cone_refl. 
HB.instance Definition _ := IsLeftCoreflection.Build _ _ Square_Cone Square_Cone_corefl. 
HB.instance Definition _ := IsAdjointEquivalenceL.Build _ _ Square_Cone. 
HB.instance Definition _ := ADJOINTEQUIVALENCE.copy Cone_Square (adj Square_Cone). 


(** * characterisation of pullbacks as limits *)

Lemma terminal_square_limit (x: Square): terminal x -> is_limit (Square_Cone x).
Proof. exact/radj.preserve_terminal. Defined.
Lemma limit_terminal_square (x: Cone): is_limit x -> terminal (Cone_Square x).
Proof. exact/radj.preserve_terminal. Defined.

Lemma pullback_limit x p q (H: is_pullback (x:=x) f g p q): is_limit (Square_Cone (square_above_ H.1)). 
Proof. exact/terminal_square_limit/pullback_terminal. Defined.

Lemma limit_pullback x: is_limit x -> @is_pullback 𝐂 a b (Cone_Square x) y f g pi1 pi2. 
Proof. move=>/limit_terminal_square. exact/terminal_pullback. Defined.

Section s.
  Variable x: Limit diagram.
  Let x' := SPAN.sort (Cone_Square (TERMINAL.sort x)).
  HB.instance Definition _ := IsSpan.Build _ a b x' pi1 pi2. 
  HB.instance Definition _ := IsSquareAbove.Build _ a b y f g x' squareAbove. 
  HB.instance Definition _ := IsPullback.Build _ a b y f g x' (limit_pullback terminalP).
  Definition Limit_Pullback: Pullback f g := x'. 
End s.

Section s.
  Variable x: Pullback f g.
  Let x' := Square_Cone (PULLBACK.sort x).
  HB.instance Definition _ := IsTerminal.Build (cone diagram) x' (pullback_limit pullbackP).
  Definition Pullback_Limit: Limit diagram := pullbacks_as_limits_x'__canonical__cat_TERMINAL. 
End s.


End s.

Definition eta (D: Diagram) := diagram (Fhom D shape.cl) (Fhom D shape.cr).
Definition diagram_eta (D: Diagram): eta D ≃ D.
Proof.
  unshelve apply: iso_ntx.
  - move=>[]; exact: idmap.
  - move=>_ _[]//; cbn; cat. 
Defined.

Definition Limit_eta (D: Diagram): Limit (eta D) -> Limit D.
Proof. exact/(radj.preserve_Terminal (transport_cone (diagram_eta D): RightAdjoint _ _)). Defined.

End s.

HB.factory Record PullbackOfLim 𝐂 & CATLIM shape.cospan 𝐂 := {}.
HB.builders Context 𝐂 & PullbackOfLim 𝐂.
HB.instance Definition _ := HasPullbacks.Build 𝐂 (fun _ _ _ f g => Limit_Pullback (lim (diagram f g))).
HB.end.

HB.factory Record LimOfPullback 𝐂 & CATPB 𝐂 := {}.
HB.builders Context 𝐂 & LimOfPullback 𝐂.
HB.instance Definition _ := HasLimits.Build shape.cospan 𝐂
                              (fun D => Limit_eta (Pullback_Limit (pb (Fhom D shape.cl) (Fhom D shape.cr)))).
HB.end.
