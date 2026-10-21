(** * more on (co)cartesian monoidal categories *)

Require Export monoidal_def adjunction coproduct.
From Stdlib Require Import ProofIrrelevance. (* TO REMOVE *)
Require Import arewrite.

Local Open Scope cat_scope.

Definition cartesian (𝐂: Type) := 𝐂.
Definition cocartesian (𝐂: Type) := 𝐂.

(** Cartesian monoidal structure of categories with finite products *)
Section s.
Context {𝐂: CatProd}.

Definition PROD (x: ob 𝐂 ∧ ob 𝐂): ob 𝐂 := x.1 × x.2. 
Program Definition _PROD_functor := @IsFunctor'.Build _ _ PROD (fun x y f => hprod f.1 f.2) _ _ _.
Next Obligation. 
  move=>/=a b f g [fg1 fg2]; apply: pair_eqv; exact: comp_eqv. 
Qed.
Next Obligation. intro. exact: prod_id. Qed.
Next Obligation. intros. exact: prod_comp. Qed.
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


(** lifting terminal objects to functors *)
Section s.
Context (𝐂: PreCat) {𝐃: Cat1}.
Section s.
Definition Fone: Functor 𝐂 𝐃 := cst one.
Lemma terminal_Fone: terminal Fone.
Proof.
  move=>F. split. unshelve esplit. move=>a. exact/term.
  split; split=>a b f. exact/termU.
  move=>i j. cbn=>a. exact/termU.
Defined.
HB.instance Definition _ := IsTerminal.Build _ Fone terminal_Fone.
End s.
HB.instance Definition _ :=
  Has1.Build (Functor 𝐂 𝐃) cartesian_Fone__canonical__cat_TERMINAL.
End s.


(** lifting binary products to functors *)
Section s.
Context (𝐂: PreCat) {𝐃: CatBProd}.
Section s.
Variables (F G: Functor 𝐂 𝐃).
Definition Fprod (a: ob 𝐂): ob 𝐃 := F a × G a.
HB.instance Definition _ := IsBarePreFunctor.Build 𝐂 𝐃 Fprod (fun a b f => hprod (Fhom F f) (Fhom G f)).
Lemma _Fprod_prefunctor: IsPreFunctor' 𝐂 𝐃 Fprod.
Proof. split=>a b f g H/=. apply: prod_eqv; exact/Fhom_eqv. Qed.
HB.instance Definition _ := _Fprod_prefunctor.
Lemma _Fprod_functor: IsFunctor 𝐂 𝐃 Fprod.
Proof.
  split.
  - move=>a. cbn. by rewrite 2!Fidmap prod_id.
  - move=>a b c f g. cbn. by rewrite 2!Fcomp prod_comp.
Qed.
HB.instance Definition _ := _Fprod_functor.
Definition Fprod_: Functor _ _ := Fprod.

Definition Fpi1: TX Fprod F := fun _ => pi1.
Lemma _Fpi1_natural: IsNatural _ _ _ _ Fpi1.
Proof. split=>a b f. cbn. by rewrite pair1. Qed.
HB.instance Definition _ := _Fpi1_natural.

Definition Fpi2: TX Fprod G := fun _ => pi2.
Lemma _Fpi2_natural: IsNatural _ _ _ _ Fpi2.
Proof. split=>a b f. cbn. by rewrite pair2. Qed.
HB.instance Definition _ := _Fpi2_natural.

HB.instance Definition _ := IsSpan.Build _ F G Fprod_ (Fpi1: NTX _ _) (Fpi2: NTX _ _).
Lemma product_Fprod: product F G Fprod_ pi1 pi2.
Proof.
  move=>H p q. split. unshelve esplit. unshelve esplit.
  move=>a. exact/(pair (p a) (q a)).
  split; split=>a b f. cbn. rewrite /hprod. apply/prod_ext. split.
  rewrite 2!compoA 2!pair1 -compoA pair1; exact/natural.
  rewrite 2!compoA 2!pair2 -compoA pair2; exact/natural.
  by cbn;split=>a/=; apply pairE.
  move=>/=[f Hf] [g Hg]. cbn=>a.
  apply: unicity_sig. apply: prodP. exact: p. exact: q.
  split. apply (Hf.1 a). apply (Hf.2 a).
  split. apply (Hg.1 a). apply (Hg.2 a).
Defined.
HB.instance Definition _ := IsProduct.Build _ F G Fprod_ product_Fprod.
End s.
HB.instance Definition _ :=
  HasBinaryProducts.Build (Functor 𝐂 𝐃) cartesian_Fprod___canonical__product_PRODUCT.
End s.


(** coCartesian monoidal structure of categories with finite coproducts *)
Section s.
Context {𝐂: CatCoprod}.

Definition COPROD (x: ob 𝐂 ∧ ob 𝐂): ob 𝐂 := x.1 + x.2.
Program Definition _COPROD_functor := @IsFunctor'.Build _ _ COPROD (fun x y f => hcoprod f.1 f.2) _ _ _.
Next Obligation.
  move=>/=a b f g [fg1 fg2]; apply: copair_eqv; exact: comp_eqv.
Qed.
Next Obligation. intro. exact: coprod_id. Qed.
Next Obligation. intros. exact: coprod_comp. Qed.
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

(** lifting initial objects to functors *)
Section s.
Context (𝐂: PreCat) {𝐃: Cat0}.
Section s.
Definition Fzero: Functor 𝐂 𝐃 := cst zero.
Lemma initial_Fzero: initial Fzero.
Proof.
  move=>/=F.
  move: (@terminal_Fone (𝐂^op) (𝐃^op)).
  (* TODO: optimise duality *)
  rewrite /terminal/initial. cbn.
  move=>/(_ (funcop F)). unshelve apply: unique_impl.
  intro n. unshelve esplit. move=>a. exact: (n a).
  split;split=>a b f. symmetry; exact: (natural n).
  intro n. unshelve esplit. move=>a. exact: (n a).
  split;split=>a b f. symmetry; exact: (natural n).
  done.
Defined.
HB.instance Definition _ := IsInitial.Build _ Fzero initial_Fzero.
End s.
HB.instance Definition _ :=
  Has0.Build (Functor 𝐂 𝐃) cartesian_Fzero__canonical__cat_INITIAL.
End s.

(** lifting binary coproducts to functors *)
Section s.
Context (𝐂: PreCat) {𝐃: CatBCoprod}.
Section s.
Variables (F G: Functor 𝐂 𝐃).
Definition Fcoprod: Functor 𝐂 𝐃 := opfunc' (opfunc F × opfunc G).
Definition Fin1: F ~> Fcoprod := ntxop' (pi1 (s := opfunc F × opfunc G)): NTX _ _.
Definition Fin2: G ~> Fcoprod := ntxop' (pi2 (s := opfunc F × opfunc G)): NTX _ _.
HB.instance Definition _ := IsCospan.Build _ F G Fcoprod Fin1 Fin2.
Lemma coproduct_Fcoprod: coproduct F G Fcoprod in1 in2.
  apply: product_op. 
  move: (@product_Fprod _ _ (opfunc F) (opfunc G))=>/product_terminal H.
  (* need to lift the adjuction to spans *)
  Fail move: (radj.preserve_terminal opfunc' H).
Admitted.
HB.instance Definition _ := IsCoproduct.Build _ F G Fcoprod coproduct_Fcoprod.
End s.
HB.instance Definition _ :=
  HasBinaryCoproducts.Build (Functor 𝐂 𝐃) cartesian_Fcoprod__canonical__coproduct_COPRODUCT.
End s.
