(** * characterisation of products as limits *)

Require Import cat morphisms span product limit.
Require Import shape functor adjunction.

Open Scope cat_scope.

(** ** representation of spans as cones over the discrete two-elements quiver *)

Section s.
Context {𝐂: Cat}.

Abbreviation Shape := (shape.discrete bool).
Abbreviation Diagram := (Diagram Shape 𝐂).

Section s.
Variables (a b: ob 𝐂).

Definition diagram: Diagram.
  exists (fun c => if c then a else b).
  done.
Defined.

Abbreviation Cone := (cone diagram).

Definition Span_Cone (x: Span a b): Cone.
  exists (Span_sort x). 
  exists (fun c => if c return Span_sort x ~> diagram c then pi1 else pi2).
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


(** * characterisation of products as limits *)

Lemma terminal_span_limit (x: Span a b): terminal x -> is_limit (Span_Cone x).
Proof. exact/radj.preserve_terminal. Defined.
Lemma limit_terminal_span (x: Cone): is_limit x -> terminal (Cone_Span x).
Proof. exact/radj.preserve_terminal. Defined.

Lemma product_limit x p q: product a b x p q -> is_limit (Span_Cone (span_ p q)). 
Proof. move=>/product_terminal. exact/terminal_span_limit. Defined.

Lemma limit_product x: is_limit x -> product a b (Cone_Span x) pi1 pi2. 
Proof. move=>/limit_terminal_span. exact/terminal_product. Defined.

Section s.
  Variable x: Limit diagram.
  Let y := SPAN.sort (Cone_Span (TERMINAL.sort x)).
  HB.instance Definition _ := IsSpan.Build _ a b y pi1 pi2. 
  HB.instance Definition _ := IsProduct.Build _ a b y (limit_product terminalP).
  Definition Limit_Product: Product a b := y. 
End s.

Section s.
  Variable x: Product a b.
  Let y := Span_Cone (PRODUCT.sort x).
  HB.instance Definition _ := IsTerminal.Build (cone diagram) y (product_limit productP).
  Definition Product_Limit: Limit diagram := products_as_limits_y__canonical__cat_TERMINAL. 
End s.


End s.

Definition diagram_eta (D: Diagram): diagram (D true) (D false) ≃ D.
Proof.
  unshelve apply: iso_ntx.
  - move=>[]; exact: idmap.
  - done.
Defined.

Definition Limit_eta (D: Diagram): Limit (diagram (D true) (D false)) -> Limit D.
Proof. exact/(radj.preserve_Terminal (transport_cone (diagram_eta D): RightAdjoint _ _)). Defined.

End s.

HB.factory Record BProdOfLim 𝐂 & CATLIM (shape.discrete bool) 𝐂 := {}.
HB.builders Context 𝐂 & BProdOfLim 𝐂.
HB.instance Definition _ := HasBinaryProducts.Build 𝐂 (fun a b => Limit_Product (lim (diagram a b))).
HB.end.

HB.factory Record LimOfBProd 𝐂 & CATBPROD 𝐂 := {}.
HB.builders Context 𝐂 & LimOfBProd 𝐂.
HB.instance Definition _ := HasLimits.Build (shape.discrete bool) 𝐂
                              (fun D => Limit_eta (Product_Limit (prod (D true) (D false)))).
HB.end.
