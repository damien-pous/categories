(** * the category of setoids *)

Require Import functor coproduct.
From Stdlib Require Import List.

Local Open Scope cat_scope.

(*
  the rest of the library requires OBJECT < SETOID
  to equip isomorphisms and natural transformations with a setoid structure

  thus it clashes here were we need SETOID < OBJECT 
 *)
Unset Universe Checking.

Abbreviation Setoid := Setoid.type.
Abbreviation SFunctor := (Functor Setoid Setoid).

(** ** the category of setoids *)

HB.instance Definition _ := IsQuiver.Build Setoid setoid_morphism.type.
HB.instance Definition _ := IsPreCat.Build Setoid (fun _ => setoid_id) (fun _ _ _ f g => setoid_comp g f).
Lemma _setoid_cat: IsCat Setoid.
Proof. split=>//*??????. exact/setoid_comp_eqv. Qed.
HB.instance Definition _ := _setoid_cat.

(** ** characterisation of epis/monos in setoids  *)

Section s.
Context [A B: Setoid] (f: A ~> B).

Lemma setoid_is_mono: is_mono f <-> injective f.
Proof.
  split.
  - move=>M x y eq.
    exact: ((M _ (const x: _ -eqv-> _) (const y: _ -eqv-> _) _ (f x))).
  - move=>H X g h E/=. cbn=>x. apply: H. exact: E.
Qed.

(* Lemma setoid_is_regmono: iffT (is_regmono f) (forall b, (exists a, f a ≡ b) -> { a | f a ≡ b }). *)
(* Proof. *)
(*   split. *)
(* Admitted. *)

Lemma setoid_is_epi: is_epi f <-> surjective f.
Proof.
  split.
  - move=>E b.
    set g := fun b => (exists a, f a ≡ b).
    have eg: Proper (eqv ==> eqv) g.
    by move=>?? e/=; rewrite /g; setoid_rewrite e.
    lapply (E (Prop: Setoid) (mk_ext g eg: B -eqv-> Prop) (const True: B-eqv->Prop)).
    move=>/(_ b)/=[_ /(_ I)[a]]. by exists a.
    move=>a; split=>//_. by exists a. 
  - move=>H X g h E. cbn=>b. case: (H b)=>a <-. exact: E.
Qed.

(* Lemma setoid_is_regepi: iffT (is_regepi f) ... *)
(* Proof. *)
(*   split. *)
(* Admitted. *)

End s.

Lemma setoid_mono [A B: Setoid] (f: A ↪ B): injective (MONO.sort f).
Proof. exact/setoid_is_mono/monoP. Qed.

Lemma setoid_epi [A B: Setoid] (f: A ↠ B): surjective (EPI.sort f).
Proof. exact/setoid_is_epi/epiP. Qed.


(** ** concrete functors in setoids *)

(** option functor *)
Definition setoid_option (A: Setoid): Setoid := option A. 
Lemma _setoid_option_map (A B: Setoid) (f: A-eqv->B):
  isExtensional _ _ (option_map f).
Proof. split. move=>[a|][a'|]//=. exact: (extensional f). Qed.
HB.instance Definition _ A B f := @_setoid_option_map A B f.
Definition setoid_option_map (A B: Setoid) (f: A-eqv->B): setoid_option A -eqv-> setoid_option B :=
  option_map f.

HB.instance Definition _ :=
  IsBarePreFunctor.Build Setoid Setoid setoid_option setoid_option_map. 
Lemma _setoid_option_prefunctor: IsPreFunctor' _ _ setoid_option.
Proof. split. cbn=> A B f g fg [a|]//=. exact: fg. Qed.
HB.instance Definition _ := _setoid_option_prefunctor.
Lemma _setoid_option_functor: IsFunctor _ _ setoid_option.
Proof.
  split.
  - by cbn=>A[a|]. 
  - by cbn=>A B C f g [a|].
Qed.
HB.instance Definition _ := _setoid_option_functor.

(** list functor *)
Definition setoid_list (A: Setoid): Setoid := list A. 
Lemma _setoid_list_map (A B: Setoid) (f: A-eqv->B):
  isExtensional _ _ (List.map f).
Proof.
  split. elim=>[|a p IH][|b q]//=.
  move=>[??]. split=>//. exact: (extensional f). exact: IH.
Qed.
HB.instance Definition _ A B f := @_setoid_list_map A B f.
Definition setoid_list_map (A B: Setoid) (f: A-eqv->B): setoid_list A -eqv-> setoid_list B :=
  List.map f.

HB.instance Definition _ :=
  IsBarePreFunctor.Build Setoid Setoid setoid_list setoid_list_map. 
Lemma _setoid_list_prefunctor: IsPreFunctor' _ _ setoid_list.
Proof. split. cbn=> A B f g fg. by elim=>[|a p IH]. Qed.
HB.instance Definition _ := _setoid_list_prefunctor.
Lemma _setoid_list_functor: IsFunctor _ _ setoid_list.
Proof.
  split.
  - cbn=>A. by elim. 
  - cbn=>A B C f g. by elim.
Qed.
HB.instance Definition _ := _setoid_list_functor.


(** power functor *)
(* TODO: integrate into closedness / do families instead *)

Section s.
Variable A: Setoid.
Definition setoid_power (X: Setoid): Setoid := A -eqv-> X. 
HB.instance Definition _ :=
  IsBarePreFunctor.Build Setoid Setoid setoid_power (fun _ _ f => mk_ext (setoid_comp f) _).
Lemma _setoid_power_prefunctor: IsPreFunctor' _ _ setoid_power.
Proof. split=> B C f g fg. cbn=>h a. exact: fg. Qed.
HB.instance Definition _ := _setoid_power_prefunctor.
Lemma _setoid_power_functor: IsFunctor _ _ setoid_power.
Proof. by split; cbn. Qed.
HB.instance Definition _ := _setoid_power_functor.
End s.


(** ** (co)Cartesian structure of setoids *)

(** initial object in setoids *)

Definition empty_setoid: Setoid := False.
Lemma _initial_setoid: @IsInitial Setoid empty_setoid.
Proof.
  split. intro. split. exact: (mk_ext empty_fun).
  by cbn. 
Defined.
HB.instance Definition _ := _initial_setoid.
(* TOFIX: why is this failing? *)
Fail Definition setoid_zero: Initial Setoid := empty_setoid.
Definition setoid_zero: Initial Setoid := setoid_empty_setoid__canonical__cat_INITIAL. 
HB.instance Definition _ := Has0.Build Setoid setoid_zero.

(** terminal object in setoids *)

Definition unit_setoid: Setoid := Datatypes.unit.
Lemma _terminal_setoid: IsTerminal Setoid unit_setoid.
Proof.
  split. intro. split. exact: (mk_ext unit_fun).
  by cbn. 
Defined.
HB.instance Definition _ := _terminal_setoid.
(* TOFIX: why is this failing? *)
Fail Definition setoid_one: Terminal Setoid := unit_setoid.
Definition setoid_one: Terminal Setoid := setoid_unit_setoid__canonical__cat_TERMINAL. 
HB.instance Definition _ := Has1.Build Setoid setoid_one.

(** products in setoids *)

Section s.
Variables A B: Setoid.
Definition setoid_prod: Setoid := A ∧ B.
Definition setoid_pi1: setoid_prod ~> A := mk_ext fst _. 
Definition setoid_pi2: setoid_prod ~> B := mk_ext snd _.
HB.instance Definition _ := IsSpan.Build Setoid A B setoid_prod setoid_pi1 setoid_pi2.
Lemma _setoid_prod: IsProduct Setoid A B setoid_prod.
Proof.
  split. intros X p q. split.
  unshelve eexists (mk_ext (fun x => (p x, q x)) _).
  by split=>/=; apply: extensional.
  by split.
  move=>[f /=[f1 f2]] [g /=[g1 g2]]. cbn=>x; split.
  setoid_rewrite (g1 x). exact: f1. 
  setoid_rewrite (g2 x). exact: f2.
Defined.
HB.instance Definition _ := _setoid_prod.
Fail Definition setoid_prod_: Product A B := setoid_prod.
Definition setoid_prod_: Product A B := setoid_setoid_prod__canonical__product_PRODUCT. 
End s.
HB.instance Definition _ := HasBinaryProducts.Build Setoid setoid_prod_.

(** coproducts in setoids *)

Section s.
Variables A B: Setoid.
Definition setoid_sum: Setoid := sum A B.
Definition setoid_in1: A ~> setoid_sum := mk_ext inl _. 
Definition setoid_in2: B ~> setoid_sum := mk_ext inr _.
HB.instance Definition _ := IsCospan.Build Setoid A B setoid_sum setoid_in1 setoid_in2.
Lemma _setoid_coprod: IsCoproduct Setoid A B setoid_sum.
Proof.
  split. intros X i j. split.
  unshelve eexists (mk_ext (fun x => match x with inl a => i a | inr b => j b end) _).
  by move=>[a|b][a'|b']//H; apply: extensional.
  done.
  move=>[f /=[f1 f2]] [g /=[g1 g2]]. move=>[a|b]/=. 
  setoid_rewrite (g1 a). exact: f1. 
  setoid_rewrite (g2 b). exact: f2.
Defined.
HB.instance Definition _ := _setoid_coprod.
Fail Definition setoid_sum_: Coproduct A B := setoid_sum.
Definition setoid_sum_: Coproduct A B := setoid_setoid_sum__canonical__coproduct_COPRODUCT. 
End s.
HB.instance Definition _ := HasBinaryCoproducts.Build Setoid setoid_sum_.

