Require Export cat morphisms span cospan product coproduct limit colimit.
Require Export shape functor adjunction monoidal_def cartesian.

Open Scope cat_scope.

(** ** representation of spans as cones over the appropriate shape *)

Section s.
Context {𝐂: Cat} (a b: ob 𝐂).

Abbreviation Shape := (Diagram (shape.discrete bool) 𝐂).
Definition shape: Shape.
  exists (fun c => if c then a else b).
  done.
Defined.
Abbreviation Cone := (cone shape).

Definition Span_Cone (x: Span a b): Cone.
  exists (Span_sort x). 
  exists (fun c => if c return Span_sort x ~> shape c then pi1 else pi2).
  done. 
Defined.
Definition Cone_Span (c: Cone): Span a b :=
  span (cone_mor c true) (cone_mor c false).

Lemma _Span_Cone_functor: IsFunctor _ _ Span_Cone.
Proof.
  unshelve eexists.
  - move=>x y h. exists (Spanhom_sort h).
    abstract by case; apply (SpanH h).
  - by move=>x y h h'.
  - by move=>x.
  - by move=>x y z f g.
Defined.
HB.instance Definition _ := _Span_Cone_functor. 

Lemma _Cone_Span_functor: IsFunctor _ _ Cone_Span.
Proof.
  unshelve eexists.
  - move=>x y h. exists (conehom_sort h).
    exact: (conehomP h true, conehomP h false).
  - by move=>x y h h'.
  - by move=>x.
  - by move=>x y z f g.
Defined.
HB.instance Definition _ := _Cone_Span_functor. 

Program Definition Span_Cone_adj: adjunction Span_Cone Cone_Span := Adj.mk _ _ _ _.
Next Obligation.
  unshelve eexists. exact: (fun c => idmap c).
  abstract by (split;split=>x y f; cbn; cat).
Defined.
Next Obligation.
  unshelve eexists. cbn=>c.
  unshelve eexists. cbn. exact: idmap.
  abstract by (case=>/=; rewrite cats).
  abstract by (split; split=>x y f; cbn; rewrite !cats).
Defined.
Next Obligation. cbn=>c. cat. Qed.
Next Obligation. cbn=>c. cat. Qed.
Lemma Span_Cone_refl: Adj.is_reflection Span_Cone_adj.
  unshelve eexists. cbn=>c.
  unshelve eexists. cbn. exact: idmap.
  abstract by (case=>/=; rewrite cats).
  abstract by split; cbn; cat. 
Defined.
Lemma Span_Cone_corefl: Adj.is_coreflection Span_Cone_adj.
  unshelve eexists. exact: (fun c => idmap c).
  abstract by split; cbn; cat. 
Defined.

HB.instance Definition _ := IsPreAdjointF.Build _ _ Span_Cone Cone_Span. 
HB.instance Definition _ := IsLeftAdjoint.Build _ _ Span_Cone Span_Cone_adj. 
HB.instance Definition _ := IsLeftReflection.Build _ _ Span_Cone Span_Cone_refl. 
HB.instance Definition _ := IsLeftCoreflection.Build _ _ Span_Cone Span_Cone_corefl. 
HB.instance Definition _ := IsAdjointEquivalenceL.Build _ _ Span_Cone. 
HB.instance Definition _ := ADJOINTEQUIVALENCE.copy Cone_Span (adj Span_Cone). 

End s.

(** ** lifting various structures through adjunctions *)

HB.factory Record Has0ThroughAdj (𝐃: Cat0) 𝐂 & CAT 𝐂 := { F: LeftAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & Has0ThroughAdj 𝐃 𝐂.
Definition Fzero := F zero.
Arguments Fzero/.
HB.instance Definition _ := IsInitial.Build 𝐂 Fzero (ladj.preserve_Initial F zero).
HB.instance Definition _ := Has0.Build 𝐂 (Fzero: Initial _).
HB.end.

HB.factory Record Has1ThroughRAdj (𝐃: Cat1) 𝐂 & CAT 𝐂 := { F: RightAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & Has1ThroughRAdj 𝐃 𝐂.
Definition Fone := F one.
Arguments Fone/.
HB.instance Definition _ := IsTerminal.Build 𝐂 Fone (radj.preserve_Terminal F one).
HB.instance Definition _ := Has1.Build 𝐂 (Fone: Terminal _).
HB.end.

HB.factory Record HasBProdThroughAdj (𝐃: CatBProd) 𝐂 & CAT 𝐂 := { F: RightAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasBProdThroughAdj 𝐃 𝐂.
Definition Fprod a b := F (prod (adj F a) (adj F b)).
Arguments Fprod _ _/.
HB.instance Definition _ a b := IsSpan.Build 𝐂 a b (Fprod a b) sorry sorry.
HB.instance Definition _ a b := IsProduct.Build 𝐂 a b (Fprod a b) sorry.
HB.instance Definition _ := HasBinaryProducts.Build 𝐂 (fun a b => Fprod a b: Product a b).
HB.end.

HB.factory Record HasBCoprodThroughAdj (𝐃: CatBCoprod) 𝐂 & CAT 𝐂 := { F: LeftAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasBCoprodThroughAdj 𝐃 𝐂.
Definition Fcoprod a b := F (coprod (adj F a) (adj F b)).
Arguments Fcoprod _ _/.
HB.instance Definition _ a b := IsCospan.Build 𝐂 a b (Fcoprod a b) sorry sorry.
HB.instance Definition _ a b := IsCoproduct.Build 𝐂 a b (Fcoprod a b) sorry.
HB.instance Definition _ := HasBinaryCoproducts.Build 𝐂 (fun a b => Fcoprod a b: Coproduct a b).
HB.end.

(** lifting binary coproducts to functors *)
HB.instance Definition _ (𝐂: Cat) {𝐃: CatBCoprod} :=
  HasBCoprodThroughAdj.Build (Functor 𝐂^op 𝐃^op)^op (Functor 𝐂 𝐃) deopfunc.

(* TODO: lift pullbacks/pushouts through adjunctions *)
