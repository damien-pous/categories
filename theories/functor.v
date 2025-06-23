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

(** rewriting tuple *)
Definition cats := (@Fidmap, cats, @Fcomp)%core.


(** identity functor *)
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreFunctor.Build 𝐂 𝐂 idfun (fun a b => setoid_id).
HB.instance Definition _ (𝐂: PreCat) :=
  IsFunctor.Build 𝐂 𝐂 idfun (fun=> eqv_refl) (fun _ _ _ _ _ => eqv_refl).
Definition functor_id {𝐂: PreCat} := idfun: Functor 𝐂 𝐂.

(** composition of functors *)
HB.instance Definition _ {𝐂 𝐃 𝐄: Quiver} {F: PreFunctor 𝐂 𝐃} {G: PreFunctor 𝐃 𝐄} :=
  IsPreFunctor.Build 𝐂 𝐄 (types_comp G F) (fun _ _ => setoid_comp (Fhom G) (Fhom F)).
Program Definition _comp_functor {𝐂 𝐃 𝐄: PreCat} {F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  IsFunctor.Build 𝐂 𝐄 (types_comp G F) _ _.
Next Obligation. intros. cbn. by rewrite !cats. Qed.
Next Obligation. intros. cbn. by rewrite !cats. Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_comp_functor 𝐂 𝐃 𝐄 F G.
Definition functor_comp {𝐂 𝐃 𝐄: PreCat} (F: Functor 𝐂 𝐃) (G: Functor 𝐃 𝐄): Functor 𝐂 𝐄 :=
  types_comp G F.

(** constant functor *)
Definition cst {𝐂 𝐃: Quiver} (D: 𝐃) := fun of 𝐂 => D.
HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (D: 𝐃) :=
  IsPreFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) :=
  IsFunctor.Build 𝐂 𝐃 (cst D) (fun=> eqv_refl)
    (fun _ _ _ _ _ => eqv_sym _ _ (compo1 idmap)).
Definition functor_cst {𝐂: PreCat} {𝐃: Cat} (D: 𝐃): Functor 𝐂 𝐃 :=
  cst D.

Section s.
  Context {𝐂 𝐃: PreCat}.
  Variables (F: Functor 𝐂 𝐃) (A B: 𝐂) (i: A ≃ B).
  Program Definition _functor_iso := @IsIso.Build _ _ _ (Fhom F i) (Fhom F i⁻¹) _ _.
  Next Obligation. intros. by rewrite -Fcomp isoK Fidmap. Qed.
  Next Obligation. intros. by rewrite -Fcomp isoK' Fidmap. Qed.
  (* forgetful inheritance: why?? *)
  (* HB.instance Definition _ := _functor_iso. *)
  Definition Fiso: F A ≃ F B := HB.pack_for (F A ≃ F B) (Fhom F i: F A ~> F B) _functor_iso.
  Lemma FisoE: Fiso⁻¹ = Fhom F i⁻¹.
  Proof. done. Qed.
End s.


(** * Natural transformations *)

(** naturality *)
HB.mixin Record IsNatural {𝐂: Quiver} {𝐃: PreCat} (F G: PreFunctor 𝐂 𝐃) (n : forall X, F X ~> G X) :=
  { #[canonical=no] natural: forall (X Y: 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X }.
#[short(type="ntx")]
HB.structure Definition Natural {𝐂 𝐃} F G :=
  { n of @IsNatural 𝐂 𝐃 F G n }.
Arguments natural {_ _ _ _} _ [_ _] _.
Definition mk_ntx {𝐂: Quiver} {𝐃: PreCat} (F G: PreFunctor 𝐂 𝐃)
  (n : forall X, F X ~> G X) (H: forall (X Y: 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X)
  := HB.pack_for (ntx F G) n (IsNatural.Build _ _ F G n H).
Arguments mk_ntx {_ _} _ _ _ _.

(** setoid structure on natural transformations *)
HB.instance Definition _ (𝐂: Quiver) (𝐃: PreCat) (F G: PreFunctor 𝐂 𝐃) :=
  Setoid.copy (ntx F G) (kernel (@Natural.sort 𝐂 𝐃 F G)).

(** category of functors and natural transformations *)
HB.instance Definition _  (𝐂: Quiver) (𝐃: PreCat) :=
  IsQuiver.Build (PreFunctor 𝐂 𝐃) (@ntx 𝐂 𝐃).
HB.instance Definition _  (𝐂 𝐃: PreCat) :=
  IsQuiver.Build (Functor 𝐂 𝐃) (@ntx 𝐂 𝐃).

Definition ntx_id {𝐂 𝐃: PreCat} (F: PreFunctor 𝐂 𝐃) :=
  fun X => \idmap (F X).
Arguments ntx_id {_ _} _ _ /. 
Lemma _ntx_id_natural (𝐂 𝐃: Cat) (F: PreFunctor 𝐂 𝐃):
  IsNatural 𝐂 𝐃 F F (ntx_id F).
Proof. by constructor=>X Y f; rewrite /= !cats. Qed.
HB.instance Definition _ 𝐂 𝐃 F := @_ntx_id_natural 𝐂 𝐃 F.

Definition ntx_comp {𝐂 𝐃: PreCat} (F G H: PreFunctor 𝐂 𝐃) (m: forall X, F X ~> G X) (n: forall X, G X ~> H X) :=
  fun X => n X ∘ m X.
Arguments ntx_comp {_ _ _ _ _} _ _ _/. 
Lemma _ntx_comp_natural (𝐂 𝐃: Cat) (F G H: PreFunctor 𝐂 𝐃) (m: F ~> G) (n: G ~> H) :
  IsNatural 𝐂 𝐃 F H (@ntx_comp 𝐂 𝐃 F G H m n).
Proof.
  constructor=>A B f /=.
  by rewrite -compoA natural compoA natural compoA.
Qed.
HB.instance Definition _ 𝐂 𝐃 F G H m n := @_ntx_comp_natural 𝐂 𝐃 F G H m n.

Definition ntx_comp' {𝐂 𝐃 𝐄: PreCat} {F G: PreFunctor 𝐂 𝐃} {F' G': PreFunctor 𝐃 𝐄}
  (k: forall X, F X ~> G X) (h: forall X, F' X ~> G' X): forall X, (types_comp F' F) X ~> (types_comp G' G) X :=
  (fun X => h _ ∘ Fhom _ (k _)).
Arguments ntx_comp' {_ _ _ _ _ _ _} _ _ _/. 
Program Definition _ntx_comp'_natural {𝐂 𝐃 𝐄: Cat} {F G: Functor 𝐂 𝐃} {F' G': Functor 𝐃 𝐄}
  (k: F ~> G) (h: F' ~> G') := IsNatural.Build 𝐂 𝐄 (types_comp F' F) (types_comp G' G) (ntx_comp' k h) _.
Next Obligation.
  intros=>/=.
  rewrite natural -compoA !natural.
  rewrite compoA -Fcomp natural. 
  by rewrite !cats.
Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G F' G' k h := @_ntx_comp'_natural 𝐂 𝐃 𝐄 F G F' G' k h.

HB.instance Definition _ {𝐂 𝐃: Cat} :=
  IsPreCat.Build (PreFunctor 𝐂 𝐃)
    (fun F => ntx_id F: ntx F F)
    (fun F G H m n => ntx_comp m n: ntx F H).
HB.instance Definition _ {𝐂 𝐃: Cat} :=
  IsPreCat.Build (Functor 𝐂 𝐃)
    (fun F => ntx_id F: ntx F F)
    (fun F G H m n => ntx_comp m n: ntx F H).

Lemma _prefunctor_cat (𝐂 𝐃: Cat): IsCat (PreFunctor 𝐂 𝐃).
Proof.
  constructor; repeat intro.
  - exact: comp1o. 
  - exact: compo1. 
  - exact: compoA.
  - exact: comp_eqv.
Qed.
HB.instance Definition _ 𝐂 𝐃 := _prefunctor_cat 𝐂 𝐃.

Lemma _functor_cat (𝐂 𝐃: Cat): IsCat (Functor 𝐂 𝐃).
Proof.
  constructor; repeat intro. 
  - exact: comp1o. 
  - exact: compo1. 
  - exact: compoA. 
  - exact: comp_eqv.
Qed.
HB.instance Definition _ 𝐂 𝐃 := _functor_cat 𝐂 𝐃.

Section s.
Context {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃).
Definition functor_equiv := F ≃ G. 
Program Definition iso_ntx'
  (i: forall X, F X ≃ G X) (n: F ~> G)
  (H: forall X, n X ≡ (i X)¹): functor_equiv :=
  mk_iso n (mk_ntx G F (fun X => (i X)⁻¹) _) _ _.
Next Obligation.
  intros. cbn. rewrite -iso_switch. setoid_rewrite <-(H X).
  rewrite -compoA -natural.
  by rewrite compoA H isoK' cats. 
Qed.
Next Obligation. move=>i n H A/=. by rewrite H isoK. Qed.
Next Obligation. move=>i n H A/=. by rewrite H isoK'. Qed.

Definition iso_ntx
  (i: forall X, F X ≃ G X):
  (forall X Y h, (i Y)¹ ∘ Fhom F h ≡ Fhom G h ∘ (i X)¹) -> functor_equiv.
Proof.
  move=>N. unshelve apply: iso_ntx'.
  exact: i.
  exact: (mk_ntx _ _ (fun X => (i X)¹) N).
  done.
Defined.

Definition iso_ntx_pw_ (i: functor_equiv): forall X, F X ~> G X := fun X => (i¹ X).
HB.instance Definition _ (i: functor_equiv) X :=
  IsIso.Build _ _ _ (iso_ntx_pw_ i X) (isoK i X) (isoK' i X).
Definition iso_ntx_pw (i: functor_equiv) X: F X ≃ G X := iso_ntx_pw_ i X. 

Lemma same_functor
  (FG1: forall X, F X = G X)
  (FG2: forall (A B: 𝐂) (f: A ~> B), Fhom G f ≡ ecast' (T:=hom) (Fhom F f) (FG1 A) (FG1 B)):
  functor_equiv.
Proof.
  unshelve apply: iso_ntx.
  - intro. rewrite FG1. exact: iso_refl.
  - intros A B f. rewrite /= FG2 /ecast' /=.
    destruct (FG1 A); destruct (FG1 B).
    by rewrite !cats. 
Defined.
End s.
Coercion iso_ntx_pw: functor_equiv >-> Funclass.
Infix "≈" := functor_equiv (at level 70): cat_scope.

(* Check fun {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃) (i: F ≈ G) (X: 𝐂) => unify (i⁻¹ X)  (i X)⁻¹.  *)

Record functor_eqv {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃): Prop := { feq_iso: F ≈ G }. 

#[local] Instance Equivalence_functor_eqv {𝐂 𝐃: Cat}: Equivalence (@functor_eqv 𝐂 𝐃). 
Proof.
  split.
  -- intro h. split. apply: iso_refl.
  -- intros F G [i]. split. exact: iso_sym. 
  -- intros F G H [i] [j]. split. apply: iso_trans; eassumption.
Qed.
HB.instance Definition _ {𝐂 𝐃: Cat} := isSetoid.Build (Functor 𝐂 𝐃) _.
HB.instance Definition _ := IsQuiver.Build Cat Functor.
HB.instance Definition _ := IsPreCat.Build Cat (@functor_id) (@functor_comp).

Section strict.
Context {A B C: Cat}.
Notation "h ⊗ k" := ((ntx_comp' k h: ntx _ _): _ ~>_(Functor _ _) _). 
Notation "` F" := (ntx_id F) (at level 4).
Lemma endo_exchange {F G H: Functor A B} {F' G' H': Functor B C}
  (i: F ~> G) (j: G ~> H)
  (i': F' ~> G') (j': G' ~> H'):
  (j'⊗j) ∘ (i'⊗i) ≡ (j'∘i') ⊗ (j∘i).
Proof.
  intro X; cbn.
  rewrite -!compoA. apply comp_eqv=>//.
  by rewrite !cats natural.
Qed.

Lemma ntx_id_comp {F: Functor A B} {G: Functor B C}:
  ntx_id (types_comp G F) ≡ `G ⊗ `F.
Proof. intro X; cbn. by rewrite !cats. Qed.

Lemma ntx_comp'_eqv {F G: Functor A B} {F' G': Functor B C}:
  Proper (eqv ==> eqv ==> eqv) (@ntx_comp' _ _ _ F G F' G').
Proof. intros i i' ii j j' jj X. by rewrite /= (ii _) (jj _). Qed.

Lemma functor_comp_eqv:
  Proper (eqv ==> eqv ==> eqv) (@functor_comp A B C).
Proof.
  intros F G [i] F' G' [j]. split.
  apply: (mk_iso (j¹⊗ i¹) (j⁻¹⊗i⁻¹)).
  rewrite endo_exchange.
  etransitivity. exact: (ntx_comp'_eqv (isoK i) (isoK j)). symmetry. exact: ntx_id_comp. 
  rewrite endo_exchange.
  etransitivity. exact: (ntx_comp'_eqv (isoK' i) (isoK' j)). symmetry. exact: ntx_id_comp. 
Qed.
End strict.


Program Definition _cat_cat := IsCat.Build Cat _ _ _ _.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. intros. exact: functor_comp_eqv. Qed.
HB.instance Definition _ := _cat_cat.
