(** * the category of setoids *)

Require Import functor.
From Stdlib Require Import List.

Local Open Scope cat_scope.

(*
  the rest of the library requires OBJECT < SETOID
  to equip isomorphisms and natural transformations with a setoid structure

  thus it clashes here were we need SETOID < OBJECT 
 *)
Unset Universe Checking.

(** ** the category of setoids *)

HB.instance Definition _ := IsQuiver.Build Setoid.type setoid_morphism.type.
HB.instance Definition _ := IsPreCat.Build Setoid.type (fun _ => setoid_id) (fun _ _ _ f g => setoid_comp g f).
Lemma _setoid_cat: IsCat Setoid.type.
Proof. split=>//*??????. exact/setoid_comp_eqv. Qed.
HB.instance Definition _ := _setoid_cat.

(** ** characterisation of epis/monos in setoids  *)

Section s.
Context [A B: Setoid.type] (f: A ~> B).

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
    lapply (E (Prop: Setoid.type) (mk_ext g eg: B -eqv-> Prop) (const True: B-eqv->Prop)).
    move=>/(_ b)/=[_ /(_ I)[a]]. by exists a.
    move=>a; split=>//_. by exists a. 
  - move=>H X g h E. cbn=>b. case: (H b)=>a <-. exact: E.
Qed.

(* Lemma setoid_is_regepi: iffT (is_regepi f) ... *)
(* Proof. *)
(*   split. *)
(* Admitted. *)

End s.

Lemma setoid_mono [A B: Setoid.type] (f: A ↪ B): injective (MONO.sort f).
Proof. exact/setoid_is_mono/monoP. Qed.

Lemma setoid_epi [A B: Setoid.type] (f: A ↠ B): surjective (EPI.sort f).
Proof. exact/setoid_is_epi/epiP. Qed.


(** ** concrete functors in setoids *)

(** option functor *)
Definition setoid_option (A: Setoid.type): Setoid.type := option A. 
Lemma _setoid_option_map (A B: Setoid.type) (f: A-eqv->B):
  isExtensional _ _ (option_map f).
Proof. split. move=>[a|][a'|]//=. exact: (extensional f). Qed.
HB.instance Definition _ A B f := @_setoid_option_map A B f.
Definition setoid_option_map (A B: Setoid.type) (f: A-eqv->B): setoid_option A -eqv-> setoid_option B :=
  option_map f.

HB.instance Definition _ :=
  IsBarePreFunctor.Build Setoid.type Setoid.type setoid_option setoid_option_map. 
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
Definition setoid_list (A: Setoid.type): Setoid.type := list A. 
Lemma _setoid_list_map (A B: Setoid.type) (f: A-eqv->B):
  isExtensional _ _ (List.map f).
Proof.
  split. elim=>[|a p IH][|b q]//=.
  move=>[??]. split=>//. exact: (extensional f). exact: IH.
Qed.
HB.instance Definition _ A B f := @_setoid_list_map A B f.
Definition setoid_list_map (A B: Setoid.type) (f: A-eqv->B): setoid_list A -eqv-> setoid_list B :=
  List.map f.

HB.instance Definition _ :=
  IsBarePreFunctor.Build Setoid.type Setoid.type setoid_list setoid_list_map. 
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
