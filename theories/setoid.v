(** * the category of setoids *)

Require Import cat morphisms.
From Stdlib Require Import CMorphisms.

Local Open Scope cat_scope.

Unset Universe Checking.

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

