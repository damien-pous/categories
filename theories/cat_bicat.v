(** * the bicategory of categories *)

Require Export span functor bicat product.

Local Open Scope cat_scope.

Unset Universe Checking.

HB.instance Definition _ := IsCatQuiver.Build Cat Functor.
HB.instance Definition _ := IsPreCat.Build Cat (@functor_id) (@functor_comp).

Check Cat: CatQuiver.
Check Cat: BarePreCat.

Program Definition _cat_bicat := @IsBiCat.Build Cat _ _ _ _ _ _ _ _.
Next Obligation. intros. exact: ntx_comp'. Defined.
Next Obligation. intros. exact: ntx_comp'_eqv. Qed.
Next Obligation. cbn. intros. cat. Qed.
Next Obligation. Admitted.
Next Obligation. intros. exact: same_functor. Defined.
Next Obligation. intros. exact: same_functor. Defined.
Next Obligation. intros. exact: same_functor. Defined.
Next Obligation. cbn. intros. cat. Qed.
HB.instance Definition _ := _cat_bicat.
