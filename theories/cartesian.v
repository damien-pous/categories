(** * more on (co)cartesian monoidal categories *)

Require Export coproduct monoidal_def.
From Stdlib Require Import ProofIrrelevance. (* TO REMOVE *)

Local Open Scope cat_scope.

Definition cartesian (𝐂: Type) := 𝐂.
Definition cocartesian (𝐂: Type) := 𝐂.

Section s.
Context {𝐂: CatProd}.

Definition PROD (x: ob 𝐂 ∧ ob 𝐂): ob 𝐂 := x.1 × x.2. 
Program Definition _PROD_functor := @IsFunctor'.Build _ _ PROD (fun x y f => pair' f.1 f.2) _ _ _.
Next Obligation. 
  move=>/=a b f g [fg1 fg2]; apply: pair_eqv; exact: comp_eqv. 
Qed.
Next Obligation. intro. exact: pair'_id. Qed.
Next Obligation. intros. exact: pair'_comp. Qed.
HB.instance Definition _ := _PROD_functor.

HB.instance Definition _ := CATPROD.on (cartesian 𝐂). 
HB.instance Definition _ := HasMonoidalOps.Build (cartesian 𝐂) one PROD. 
HB.instance Definition _ := HasUIP.Build (cartesian 𝐂) (fun _ _ => proof_irrelevance _). 

Program Definition _cartesian_premonoidal :=
  @IsPreMonoidal.Build (cartesian 𝐂) prodA prodUl prodUr _ _ _.  
Next Obligation. intros a b c a' b' c' f g h. Admitted.
Next Obligation. intros a a' f. Admitted.
Next Obligation. intros a a' f. Admitted.
HB.instance Definition _ := _cartesian_premonoidal.

Program Definition _cartesian_monoidal :=
  @IsMonoidal.Build (cartesian 𝐂) _ _.
Next Obligation. intros a b c d. Admitted.
Next Obligation. intros a b. Admitted.
HB.instance Definition _ := _cartesian_monoidal.

End s.

Section s.
Context {𝐂: CatCoprod}.

Definition COPROD (x: ob 𝐂 ∧ ob 𝐂): ob 𝐂 := x.1 + x.2. 
Program Definition _COPROD_functor := @IsFunctor'.Build _ _ COPROD (fun x y f => copair' f.1 f.2) _ _ _.
Next Obligation. 
  move=>/=a b f g [fg1 fg2]; apply: copair_eqv; exact: comp_eqv. 
Qed.
Next Obligation. intro. exact: copair'_id. Qed.
Next Obligation. intros. exact: copair'_comp. Qed.
HB.instance Definition _ := _COPROD_functor.

HB.instance Definition _ := CATCOPROD.on (cocartesian 𝐂). 
HB.instance Definition _ := HasMonoidalOps.Build (cocartesian 𝐂) zero COPROD. 
HB.instance Definition _ := HasUIP.Build (cocartesian 𝐂) (fun _ _ => proof_irrelevance _). 

Program Definition _cocartesian_premonoidal :=
  @IsPreMonoidal.Build (cocartesian 𝐂) coprodA coprodUl coprodUr _ _ _.  
Next Obligation. intros a b c a' b' c' f g h. Admitted.
Next Obligation. intros a a' f. Admitted.
Next Obligation. intros a a' f. Admitted.
HB.instance Definition _ := _cocartesian_premonoidal.

Program Definition _cocartesian_monoidal :=
  @IsMonoidal.Build (cocartesian 𝐂) _ _.
Next Obligation. intros a b c d. Admitted.
Next Obligation. intros a b. Admitted.
HB.instance Definition _ := _cocartesian_monoidal.

End s.
