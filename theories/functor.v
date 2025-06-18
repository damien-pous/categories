(** * Functors and natural transformations *)

Require Export cat.

Local Open Scope cat_scope.

(** * Functors *)

(** prefunctor: a functor without laws *)
HB.mixin Record IsPreFunctor (𝐂 𝐃: Quiver) (F: 𝐂 -> 𝐃) := {
   #[canonical=no] Fhom: forall A B: 𝐂, (A ~> B) -eqv-> (F A ~> F B)
  }.
#[short(type="PreFunctor")]
HB.structure Definition prefunctor 𝐂 𝐃 :=
  { F of IsPreFunctor 𝐂 𝐃 F }.
Arguments Fhom {_ _} _ {_ _}. 

(** functor: prefunctor + laws *)
HB.mixin Record IsFunctor (𝐂 𝐃: PreCat) F of @prefunctor 𝐂 𝐃 F := {
    #[canonical=no] Fidmap: forall A: 𝐂, Fhom F (\idmap A) ≡ idmap;
    #[canonical=no] Fcomp: forall {A B C: 𝐂} (f: A ~> B) (g: B ~> C), Fhom F (g ∘ f) ≡ Fhom F g ∘ Fhom F f;
}.
#[short(type="Functor")]
HB.structure Definition functor (𝐂 𝐃: PreCat) :=
  { F of IsFunctor 𝐂 𝐃 F & }.

(** rewriting tupe *)
Definition cats := (@Fidmap,@compo1,@comp1o,@Fcomp,@compoA)%core.


(** identity functor *)
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreFunctor.Build 𝐂 𝐂 idfun (fun a b => setoid_id).
HB.instance Definition _ (𝐂: PreCat) :=
  IsFunctor.Build 𝐂 𝐂 idfun (fun=> eqv_refl) (fun _ _ _ _ _ => eqv_refl).
Definition id_functor {𝐂: PreCat} := idfun: Functor 𝐂 𝐂.

(** composition of functors *)
HB.instance Definition _ {𝐂 𝐃 𝐄: Quiver} {F: PreFunctor 𝐂 𝐃} {G: PreFunctor 𝐃 𝐄} :=
  IsPreFunctor.Build 𝐂 𝐄 (G \o F) (fun _ _ => setoid_comp (Fhom G) (Fhom F)).
Program Definition _functor_comp {𝐂 𝐃 𝐄: PreCat} {F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  IsFunctor.Build 𝐂 𝐄 (G \o F) _ _.
Next Obligation. intros. cbn. by rewrite !cats. Qed.
Next Obligation. intros. cbn. by rewrite !cats. Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_functor_comp 𝐂 𝐃 𝐄 F G.
Definition comp_functor {𝐂 𝐃 𝐄: PreCat}{F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} := G \o F: Functor 𝐂 𝐄.

(** constant functor *)
Definition cst {𝐂 𝐃: Quiver} (D: 𝐃) := fun of 𝐂 => D.
HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (D: 𝐃) :=
  IsPreFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) :=
  IsFunctor.Build 𝐂 𝐃 (cst D) (fun=> eqv_refl)
    (fun _ _ _ _ _ => eqv_sym _ _ (compo1 idmap)).
Definition cst_functor {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) := cst D: Functor 𝐂 𝐃.


(** * Natural transformations *)

(** naturality *)
HB.mixin Record IsNatural (𝐂: Quiver) (𝐃: PreCat) (F G: PreFunctor 𝐂 𝐃) (n : forall X, F X ~> G X) :=
  { #[canonical=no] natural: forall (X Y: 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X }.
HB.structure Definition Natural 𝐂 𝐃 F G :=
  { n of @IsNatural 𝐂 𝐃 F G n }.
Arguments natural {_ _ _ _} _ [_ _] _.

(** setoid structure on natural transformations *)
HB.instance Definition _ 𝐂 𝐃 F G :=
  Setoid.copy (Natural.type F G) (kernel (@Natural.sort 𝐂 𝐃 F G)).

(** category of functors and natural transformations *)
HB.instance Definition _  (𝐂: Quiver) (𝐃: PreCat) :=
  IsQuiver.Build (PreFunctor 𝐂 𝐃) (@Natural.type 𝐂 𝐃).
HB.instance Definition _  (𝐂 𝐃: PreCat) :=
  IsQuiver.Build (Functor 𝐂 𝐃) (@Natural.type 𝐂 𝐃).

Definition natural_id {𝐂 𝐃: PreCat} (F: PreFunctor 𝐂 𝐃) :=
  fun X => \idmap (F X).
Lemma natural_id_natural (𝐂 𝐃: Cat) (F: PreFunctor 𝐂 𝐃):
  IsNatural 𝐂 𝐃 F F (natural_id F).
Proof. by constructor=>X Y f; rewrite /natural_id/= !cats. Qed.
HB.instance Definition _ 𝐂 𝐃 F := @natural_id_natural 𝐂 𝐃 F.

Definition natural_comp {𝐂 𝐃: PreCat} (F G H: PreFunctor 𝐂 𝐃) (m: F ~> G) (n : G ~> H) :=
  fun X => n X ∘ m X.
Definition natural_comp_natural (𝐂 𝐃: Cat) (F G H: PreFunctor 𝐂 𝐃) m n :
  IsNatural 𝐂 𝐃 F H (@natural_comp 𝐂 𝐃 F G H m n).
Proof.
  constructor=> a b f; rewrite /natural_comp/=.
  by rewrite -compoA natural compoA natural compoA.
Qed.
HB.instance Definition _ 𝐂 𝐃 F G H m n := @natural_comp_natural 𝐂 𝐃 F G H m n.

HB.instance Definition _ {𝐂 𝐃: Cat} :=
  IsPreCat.Build (PreFunctor 𝐂 𝐃)
    (fun F => natural_id F: Natural.type F F)
    (fun F G H m n => natural_comp m n: Natural.type F H).
HB.instance Definition _ {𝐂 𝐃: Cat} :=
  IsPreCat.Build (Functor 𝐂 𝐃)
    (fun F => natural_id F: Natural.type F F)
    (fun F G H m n => natural_comp m n: Natural.type F H).

Lemma _prefunctor_cat (𝐂 𝐃: Cat): IsCat (PreFunctor 𝐂 𝐃).
Proof.
  constructor; repeat intro.
  - exact: comp1o. 
  - exact: compo1. 
  - exact: compoA.
  - exact: compoE.
Qed.
HB.instance Definition _ 𝐂 𝐃 := _prefunctor_cat 𝐂 𝐃.

Lemma _functor_cat (𝐂 𝐃: Cat): IsCat (Functor 𝐂 𝐃).
Proof.
  constructor; repeat intro. 
  - exact: comp1o. 
  - exact: compo1. 
  - exact: compoA. 
  - exact: compoE.
Qed.
HB.instance Definition _ 𝐂 𝐃 := _functor_cat 𝐂 𝐃.

Record functor_eqv {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃): Prop := { feq_iso: F ≃ G }. 

#[local] Instance Equivalence_functor_eqv {𝐂 𝐃: Cat}: Equivalence (@functor_eqv 𝐂 𝐃). 
Proof.
  split.
  -- intro h. split. apply: iso_refl.
  -- intros F G [i]. split. exact: iso_sym. 
  -- intros F G H [i] [j]. split. apply: iso_trans; eassumption.
Qed.
HB.instance Definition _ {𝐂 𝐃: Cat} := isSetoid.Build (Functor 𝐂 𝐃) _.

HB.instance Definition _ := IsQuiver.Build Cat Functor.
HB.instance Definition _ := IsPreCat.Build Cat (@id_functor) (@comp_functor).
Program Definition _cat_cat := IsCat.Build Cat _ _ _ _.
Admit Obligations.
HB.instance Definition _ := _cat_cat.
