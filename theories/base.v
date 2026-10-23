Require Export cat morphisms span cospan product coproduct limit colimit.
Require Export shape functor adjunction monoidal_def cartesian.

Open Scope cat_scope.

(** ** lifting various structures through appropriate adjunctions *)

HB.factory Record Has0ThroughAdj (𝐃: Cat0) 𝐂 & CAT 𝐂 := { F: LeftAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & Has0ThroughAdj 𝐃 𝐂.
HB.instance Definition _ := Has0.Build 𝐂 (ladj.preserve_Initial F zero).
HB.end.

HB.factory Record Has1ThroughRAdj (𝐃: Cat1) 𝐂 & CAT 𝐂 := { F: RightAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & Has1ThroughRAdj 𝐃 𝐂.
Definition Fone := F one.
HB.instance Definition _ := Has1.Build 𝐂 (radj.preserve_Terminal F one).
HB.end.

HB.factory Record HasBProdThroughAdj (𝐃: CatBProd) 𝐂 & CAT 𝐂 := { F: RightAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasBProdThroughAdj 𝐃 𝐂.
(* TODO via limits *)
Definition Fprod a b := F (prod (adj F a) (adj F b)).
Arguments Fprod _ _/.
HB.instance Definition _ a b := IsSpan.Build 𝐂 a b (Fprod a b) sorry sorry.
HB.instance Definition _ a b := IsProduct.Build 𝐂 a b (Fprod a b) sorry.
HB.instance Definition _ := HasBinaryProducts.Build 𝐂 (fun a b => Fprod a b: Product a b).
HB.end.

HB.factory Record HasBCoprodThroughAdj (𝐃: CatBCoprod) 𝐂 & CAT 𝐂 := { F: LeftAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasBCoprodThroughAdj 𝐃 𝐂.
(* TODO via colimits *)
Definition Fcoprod a b := F (coprod (adj F a) (adj F b)).
Arguments Fcoprod _ _/.
HB.instance Definition _ a b := IsCospan.Build 𝐂 a b (Fcoprod a b) sorry sorry.
HB.instance Definition _ a b := IsCoproduct.Build 𝐂 a b (Fcoprod a b) sorry.
HB.instance Definition _ := HasBinaryCoproducts.Build 𝐂 (fun a b => Fcoprod a b: Coproduct a b).
HB.end.

(** lifting binary coproducts to functors *)
HB.instance Definition _ (𝐂: Cat) {𝐃: CatBCoprod} :=
  HasBCoprodThroughAdj.Build (Functor 𝐂^op 𝐃^op)^op (Functor 𝐂 𝐃) deopfunc.
