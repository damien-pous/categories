(** * the bicategory of categories *)

Require Import cat functor bicat.

Local Open Scope cat_scope.

Unset Universe Checking.

HB.instance Definition _ := IsCatQuiver.Build Cat Functor.
HB.instance Definition _ := IsPreCat.Build Cat (@functor_id) (@functor_comp).

Check Cat: CatQuiver.
Check Cat: BarePreCat.

Program Definition _cat_bicat := @IsBiCat.Build Cat _ _ _ _ _ _ _ _ _ _.
Next Obligation. intros. exact/ntx_comp'. Defined.
Next Obligation. intros. exact/ntx_comp'_eqv. Qed.
Next Obligation. intros. exact/ntx_comp'_id. Qed.
Next Obligation. intros. exact/ntx_comp'_comp. Qed.
Next Obligation. intros. exact/iso_functor/same_diagram. Defined.
Next Obligation. intros. exact/iso_functor/same_diagram. Defined.
Next Obligation. intros. exact/iso_functor/same_diagram. Defined.
Next Obligation. cbn. intros. cat. Qed.
Next Obligation. cbn. intros. cat. Qed.
Next Obligation. cbn. intros. cat. Qed.
HB.instance Definition _ := _cat_bicat.
