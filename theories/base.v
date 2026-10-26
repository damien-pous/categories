Require Export cat morphisms span cospan product coproduct pullback pushout limit colimit.
Require Export shape functor adjunction monoidal_def cartesian.
Require Import products_as_limits coproducts_as_colimits.
Require Import pullbacks_as_limits (* pushouts_as_colimits *).

Open Scope cat_scope.

(** ** lifting various structures through appropriate adjunctions *)

HB.factory Record Has0ThroughAdj (𝐃: Cat0) 𝐂 & CAT 𝐂 := { F: LeftAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & Has0ThroughAdj 𝐃 𝐂.
HB.instance Definition _ := Has0.Build 𝐂 (ladj.preserve_Initial F zero).
HB.end.

HB.factory Record Has1ThroughRAdj (𝐃: Cat1) 𝐂 & CAT 𝐂 := { F: RightAdjoint 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & Has1ThroughRAdj 𝐃 𝐂.
HB.instance Definition _ := Has1.Build 𝐂 (radj.preserve_Terminal F one).
HB.end.

HB.factory Record HasBProdThroughAdj (𝐃: CatBProd) 𝐂 & CAT 𝐂 := { F: RightCoreflection 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasBProdThroughAdj 𝐃 𝐂.
Definition 𝐂': Type := 𝐂.
Definition 𝐃': Type := 𝐃.
HB.instance Definition _ := CAT.on 𝐂'.
HB.instance Definition _ := CATBPROD.on 𝐃'.
HB.instance Definition _ := LimOfBProd.Build 𝐃'.
HB.instance Definition _ := HasLimitsThroughAdj.Build _ 𝐃' 𝐂' F.
HB.instance Definition _ := BProdOfLim.Build 𝐂'.
HB.instance Definition _ := CATBPROD.copy 𝐂 𝐂'.
HB.end. 

HB.factory Record HasBCoprodThroughAdj (𝐃: CatBCoprod) 𝐂 & CAT 𝐂 := { F: LeftReflection 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasBCoprodThroughAdj 𝐃 𝐂.
(* TOTHINK: we could also do without [coproducts_as_limits.v], as for pushouts below *)
Definition 𝐂': Type := 𝐂.
Definition 𝐃': Type := 𝐃.
HB.instance Definition _ := CAT.on 𝐂'.
HB.instance Definition _ := CATBCOPROD.on 𝐃'.
HB.instance Definition _ := ColimOfBCoprod.Build 𝐃'.
HB.instance Definition _ := HasColimitsThroughAdj.Build _ 𝐃' 𝐂' F.
HB.instance Definition _ := BCoprodOfColim.Build 𝐂'.
HB.instance Definition _ := CATBCOPROD.copy 𝐂 𝐂'.
HB.end. 

(** lifting binary coproducts to functors *)
HB.instance Definition _ (𝐂: Cat) {𝐃: CatBCoprod} :=
  HasBCoprodThroughAdj.Build (Functor 𝐂^op 𝐃^op)^op (Functor 𝐂 𝐃) deopfunc.
HB.saturate Functor.

HB.factory Record HasPullbackThroughAdj (𝐃: CatPb) 𝐂 & CAT 𝐂 := { F: RightCoreflection 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasPullbackThroughAdj 𝐃 𝐂.
Definition 𝐂': Type := 𝐂.
Definition 𝐃': Type := 𝐃.
HB.instance Definition _ := CAT.on 𝐂'.
HB.instance Definition _ := CATPB.on 𝐃'.
HB.instance Definition _ := LimOfPullback.Build 𝐃'.
HB.instance Definition _ := HasLimitsThroughAdj.Build _ 𝐃' 𝐂' F.
HB.instance Definition _ := PullbackOfLim.Build 𝐂'.
HB.instance Definition _ := CATPB.copy 𝐂 𝐂'.
HB.end. 

HB.factory Record HasPushoutThroughAdj (𝐃: CatPo) 𝐂 & CAT 𝐂 := { F: LeftReflection 𝐃 𝐂 }.
HB.builders Context 𝐃 𝐂 & HasPushoutThroughAdj 𝐃 𝐂.
Definition 𝐂': Type := 𝐂^op.
Definition 𝐃': Type := 𝐃^op.
Definition F' := funcop F.
HB.instance Definition _ := CAT.on 𝐂'.
HB.instance Definition _ := CATPB.on 𝐃'.
HB.instance Definition _ := RIGHTCOREFLECTION.on F'. 
HB.instance Definition _ := LimOfPullback.Build 𝐃'.
HB.instance Definition _ := HasLimitsThroughAdj.Build _ 𝐃' 𝐂' F'.
HB.instance Definition _ := PullbackOfLim.Build 𝐂'.
HB.instance Definition _ := CATPO.copy 𝐂 𝐂'^op.
HB.end. 
