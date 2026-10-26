(** * characterisation of coproducts as colimits *)

Require Import cat morphisms cospan coproduct colimit.
Require Import shape functor adjunction.

Open Scope cat_scope.

(** ** representation of cocospans as cocones over the discrete two-elements quiver *)

(* TOTHINK: use duality and products_of_limits? *)

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

Abbreviation Cocone := (cocone diagram).

Definition Cospan_Cocone (x: Cospan a b): Cocone.
  exists (COSPAN.sort x). 
  exists (fun c => if c return diagram c ~> COSPAN.sort x then in1 else in2).
  done. 
Defined.
Definition Cocone_Cospan (c: Cocone): Cospan a b :=
  cospan (cocone_mor c true) (cocone_mor c false).

Lemma _Cospan_Cocone_functor: IsFunctor _ _ Cospan_Cocone.
Proof.
  unshelve eexists.
  - move=>x y h. exists (Cospanhom_sort h).
    abstract by case; apply (CospanH h).
  - by move=>x y h h'.
  - by move=>x.
  - by move=>x y z f g.
Defined.
HB.instance Definition _ := _Cospan_Cocone_functor. 

Lemma _Cocone_Cospan_functor: IsFunctor _ _ Cocone_Cospan.
Proof.
  unshelve eexists.
  - move=>x y h. exists (coconehom_sort h).
    exact: (coconehomP h true, coconehomP h false).
  - by move=>x y h h'.
  - by move=>x.
  - by move=>x y z f g.
Defined.
HB.instance Definition _ := _Cocone_Cospan_functor. 

Program Definition Cospan_Cocone_adj: adjunction Cospan_Cocone Cocone_Cospan := Adj.mk _ _ _ _.
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
Lemma Cospan_Cocone_refl: Adj.is_reflection Cospan_Cocone_adj.
  unshelve eexists. cbn=>c.
  unshelve eexists. cbn. exact: idmap.
  abstract by (case=>/=; rewrite cats).
  abstract by split; cbn; cat. 
Defined.
Lemma Cospan_Cocone_corefl: Adj.is_coreflection Cospan_Cocone_adj.
  unshelve eexists. exact: (fun c => idmap c).
  abstract by split; cbn; cat. 
Defined.

HB.instance Definition _ := IsPreAdjointF.Build _ _ Cospan_Cocone Cocone_Cospan. 
HB.instance Definition _ := IsLeftAdjoint.Build _ _ Cospan_Cocone Cospan_Cocone_adj. 
HB.instance Definition _ := IsLeftReflection.Build _ _ Cospan_Cocone Cospan_Cocone_refl. 
HB.instance Definition _ := IsLeftCoreflection.Build _ _ Cospan_Cocone Cospan_Cocone_corefl. 
HB.instance Definition _ := IsAdjointEquivalenceL.Build _ _ Cospan_Cocone. 
HB.instance Definition _ := ADJOINTEQUIVALENCE.copy Cocone_Cospan (adj Cospan_Cocone). 


(** * characterisation of coproducts as colimits *)

Lemma initial_cospan_colimit (x: Cospan a b): initial x -> is_colimit (Cospan_Cocone x).
Proof. exact/ladj.preserve_initial. Defined.
Lemma colimit_initial_cospan (x: Cocone): is_colimit x -> initial (Cocone_Cospan x).
Proof. exact/ladj.preserve_initial. Defined.

Lemma coproduct_colimit x p q: coproduct a b x p q -> is_colimit (Cospan_Cocone (cospan_ p q)). 
Proof. move=>/coproduct_initial. exact/initial_cospan_colimit. Defined.

Lemma colimit_coproduct x: is_colimit x -> coproduct a b (Cocone_Cospan x) in1 in2. 
Proof. move=>/colimit_initial_cospan. exact/initial_coproduct. Defined.

Section s.
  Variable x: Colimit diagram.
  Let y := COSPAN.sort (Cocone_Cospan (INITIAL.sort x)).
  HB.instance Definition _ := IsCospan.Build _ a b y in1 in2. 
  HB.instance Definition _ := IsCoproduct.Build _ a b y (colimit_coproduct initialP).
  Definition Colimit_Coproduct: Coproduct a b := y. 
End s.

Section s.
  Variable x: Coproduct a b.
  Let y := Cospan_Cocone (COPRODUCT.sort x).
  HB.instance Definition _ := IsInitial.Build (cocone diagram) y (coproduct_colimit coproductP).
  Definition Coproduct_Colimit: Colimit diagram := coproducts_as_colimits_y__canonical__cat_INITIAL. 
End s.


End s.

Definition diagram_eta (D: Diagram): D ≃ diagram (D true) (D false).
Proof.
  unshelve apply: iso_ntx.
  - move=>[]; exact: idmap.
  - done.
Defined.

Definition Colimit_eta (D: Diagram): Colimit (diagram (D true) (D false)) -> Colimit D.
Proof. exact/(ladj.preserve_Initial (transport_cocone (diagram_eta D): LeftAdjoint _ _)). Defined.

End s.

HB.factory Record BCoprodOfColim 𝐂 & CATCOLIM (shape.discrete bool) 𝐂 := {}.
HB.builders Context 𝐂 & BCoprodOfColim 𝐂.
HB.instance Definition _ := HasBinaryCoproducts.Build 𝐂 (fun a b => Colimit_Coproduct (colim (diagram a b))).
HB.end.

HB.factory Record ColimOfBCoprod 𝐂 & CATBCOPROD 𝐂 := {}.
HB.builders Context 𝐂 & ColimOfBCoprod 𝐂.
HB.instance Definition _ := HasColimits.Build (shape.discrete bool) 𝐂
                              (fun D => Colimit_eta (Coproduct_Colimit (coprod (D true) (D false)))).
HB.end.
