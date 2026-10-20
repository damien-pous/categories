(** * Functors, natural transformations, adjunctions *)

Require Export morphisms.
Require Import arewrite.

Local Open Scope cat_scope.

(** * Functors *)

(** bareprefunctor: a barequiver morphism *)

#[primitive] HB.mixin Record IsBarePreFunctor (𝐂 𝐃: BareQuiver) (F: ob 𝐂 -> ob 𝐃) := {
   #[canonical=no] Fhom: forall A B: ob 𝐂, (A ~> B) -> (F A ~> F B);
  }.
#[short(type="BarePreFunctor")]
HB.structure Definition BAREPREFUNCTOR 𝐂 𝐃 :=
  { F of IsBarePreFunctor 𝐂 𝐃 F }.
Arguments Fhom {_ _} _ {_ _}. 

(** prefunctor: a functor without laws *)
#[primitive] HB.mixin Record IsPreFunctor' (𝐂 𝐃: Quiver) F of @BAREPREFUNCTOR 𝐂 𝐃 F := {
   #[canonical=no] _Fhom_eqv: forall A B: ob 𝐂, Proper (eqv ==> eqv) (@Fhom _ _ F A B);
  }.
#[short(type="PreFunctor")]
HB.structure Definition PREFUNCTOR 𝐂 𝐃 :=
  { F of IsPreFunctor' 𝐂 𝐃 F & }.
Arguments Fhom {_ _} _ {_ _}. 
Instance Fhom_eqv {𝐂 𝐃: Quiver} {F: PreFunctor 𝐂 𝐃} {A B: ob 𝐂}: Proper (eqv ==> eqv) (Fhom F) := _Fhom_eqv A B. 
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) A B :=
  isExtensional.Build _ _ (@Fhom _ _ F A B) _. 

(** alternative factory, when the action on morphisms is already registered as extensional *)
HB.factory Record IsPreFunctor (𝐂 𝐃: Quiver) (F: ob 𝐂 -> ob 𝐃) := {
    Fhom: forall {A B}, (A ~> B) -eqv-> (F A ~> F B);
  }.
HB.builders Context 𝐂 𝐃 F of @IsPreFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := @IsBarePreFunctor.Build _ _ F Fhom.
  HB.instance Definition _ := @IsPreFunctor'.Build _ _ F (fun _ _ => extensional _).
HB.end.

(** functor: prefunctor + laws *)
#[primitive] HB.mixin Record IsFunctor (𝐂 𝐃: PreCat) F of @PREFUNCTOR 𝐂 𝐃 F := {
    #[canonical=no] _Fidmap: forall A: ob 𝐂, Fhom F A ≡ F A;
    #[canonical=no] _Fcomp: forall (A B C: ob 𝐂) (f: A ~> B) (g: B ~> C), Fhom F (f \; g) ≡ Fhom F f \; Fhom F g;
  }.
#[short(type="Functor")]
HB.structure Definition FUNCTOR (𝐂 𝐃: PreCat) :=
  { F of IsFunctor 𝐂 𝐃 F & }.
Definition Fidmap {𝐂 𝐃: PreCat} {F: Functor 𝐂 𝐃} {A: ob 𝐂}: Fhom F A ≡ F A := _Fidmap A.
Definition Fcomp {𝐂 𝐃: PreCat} {F: Functor 𝐂 𝐃} {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C): Fhom F (f \; g) ≡ Fhom F f \; Fhom F g := _Fcomp _ _ _ f g. 

HB.factory Record IsFunctor' (𝐂 𝐃: PreCat) (F: ob 𝐂 -> ob 𝐃) := {
   Fhom: forall {A B: ob 𝐂}, (A ~> B) -> (F A ~> F B);
   Fhom_eqv: forall {A B: ob 𝐂}, Proper (eqv ==> eqv) (@Fhom A B);
   Fidmap: forall A: ob 𝐂, Fhom A ≡ idmap (F A);
   Fcomp: forall {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C), Fhom (g ∘ f) ≡ Fhom g ∘ Fhom f;
  }.
HB.builders Context 𝐂 𝐃 F of @IsFunctor' 𝐂 𝐃 F.
  HB.instance Definition _ := IsBarePreFunctor.Build _ _ F Fhom.
  HB.instance Definition _ := IsPreFunctor'.Build _ _ F Fhom_eqv.
  HB.instance Definition _ := IsFunctor.Build _ _ F Fidmap Fcomp.
HB.end.

(** * faithful functors *)

(** faithful (pre)functor: + injectivity on morphisms *)
#[primitive] HB.mixin Record IsFaithful (𝐂 𝐃: Quiver) F of @PREFUNCTOR 𝐂 𝐃 F := {
    #[canonical=no] Fhom_inj: forall {A B} (f g: A ~> B), Fhom F f ≡ Fhom F g -> f ≡ g;
  }.
#[short(type="FaithfulPreFunctor")]
HB.structure Definition FAITHFULPREFUNCTOR 𝐂 𝐃 :=
  { F of @PREFUNCTOR 𝐂 𝐃 F & IsFaithful 𝐂 𝐃 F }.
#[short(type="FaithfulFunctor")]
HB.structure Definition FAITHFULFUNCTOR 𝐂 𝐃 :=
  { F of @FUNCTOR 𝐂 𝐃 F & IsFaithful 𝐂 𝐃 F }.
Arguments Fhom_inj {_ _} _ {_ _}.

Lemma Fhom_bij 𝐂 𝐃 (F: FaithfulPreFunctor 𝐂 𝐃) {A B: ob 𝐂} (f g: A ~> B):
  Fhom F f ≡ Fhom F g <-> f ≡ g.
Proof. split. exact:Fhom_inj. exact/Fhom_eqv. Qed.

HB.factory Record IsFaithfulPreFunctor (𝐂 𝐃: Quiver) (F: ob 𝐂 -> ob 𝐃) := {
    Fhom: forall {A B}, (A ~> B) -> (F A ~> F B);
    Fhom_bij: forall {A B} (f g: A ~> B), Fhom f ≡ Fhom g <-> f ≡ g;
  }.
HB.builders Context 𝐂 𝐃 F of @IsFaithfulPreFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := IsBarePreFunctor.Build _ _ F Fhom.
  HB.instance Definition _ := IsPreFunctor'.Build _ _ F (fun _ _ f g => proj2 (Fhom_bij f g)).
  HB.instance Definition _ := IsFaithful.Build _ _ F (fun _ _ f g => proj1 (Fhom_bij f g)).
HB.end.

(** getting category laws from faithful functors *)
HB.factory Record FaithfulSubCat (𝐃: Cat)  𝐂 of PRECAT 𝐂 := { F: FaithfulFunctor 𝐂 𝐃 }.
HB.builders Context 𝐃 𝐂 of FaithfulSubCat 𝐃 𝐂.
Program Definition _faithfulsubcat := IsCat.Build 𝐂 _ _ _ _.
Next Obligation. move=>A B f. apply: (Fhom_inj F). rewrite Fcomp Fidmap. cat. Qed.
Next Obligation. move=>A B f. apply: (Fhom_inj F). rewrite Fcomp Fidmap. cat. Qed.
Next Obligation. move=>A B C D f g h. apply: (Fhom_inj F). rewrite 4!Fcomp. cat. Qed.
Next Obligation.
  move=>A B C f f' ff g g' gg. apply: (Fhom_inj F). rewrite 2!Fcomp.
  apply: comp_eqv; exact/Fhom_eqv.
Qed.
HB.instance Definition _ := _faithfulsubcat.
HB.end. 

(** rewriting tuple *)
Definition cats := (@Fidmap, cats, @Fcomp)%core.


(** * duality *)

Definition funcop {𝐂 𝐃} (F: ob 𝐂 -> ob 𝐃): ob 𝐂^op -> ob 𝐃^op := F.
Definition funcop' {𝐂 𝐃} (F: ob 𝐂^op -> ob 𝐃^op): ob 𝐂 -> ob 𝐃 := F.

HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: BarePreFunctor 𝐂 𝐃) :=
  IsBarePreFunctor.Build _ _ (funcop F) (fun _ _ => Fhom F).
HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: BarePreFunctor 𝐂^op 𝐃^op) :=
  IsBarePreFunctor.Build _ _ (funcop' F) (fun _ _ => Fhom F).

HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂 𝐃) :=
  IsPreFunctor'.Build _ _ (funcop F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂^op 𝐃^op) :=
  IsPreFunctor'.Build _ _ (funcop' F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).

HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂 𝐃) :=
  IsFunctor.Build _ _ (funcop F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂^op 𝐃^op) :=
  IsFunctor.Build _ _ (funcop' F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).

Definition funcop12 {𝐂 𝐃} (F: ob 𝐂^op -> ob 𝐃): ob 𝐂 -> ob 𝐃^op := F.
Definition funcop21 {𝐂 𝐃} (F: ob 𝐂 -> ob 𝐃^op): ob 𝐂^op -> ob 𝐃 := F.

HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: BarePreFunctor 𝐂^op 𝐃) :=
  IsBarePreFunctor.Build _ _ (funcop12 F) (fun _ _ => Fhom F).
HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: BarePreFunctor 𝐂 𝐃^op) :=
  IsBarePreFunctor.Build _ _ (funcop21 F) (fun _ _ => Fhom F).

HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂^op 𝐃) :=
  IsPreFunctor'.Build _ _ (funcop12 F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂 𝐃^op) :=
  IsPreFunctor'.Build _ _ (funcop21 F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).

HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂^op 𝐃) :=
  IsFunctor.Build _ _ (funcop12 F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂 𝐃^op) :=
  IsFunctor.Build _ _ (funcop21 F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).

(* TODO: duality for faithful functors *)

(** extension of the normalisation tactic to deal with functors *)
Module HL.
  Export HL.
  Section s.
  Context {𝐂 𝐃: Cat} {F: Functor 𝐂 𝐃}. 
  Fixpoint map {A B} (u: hom_list A B): hom_list (F A) (F B) :=
    match u with
    | nil => nil
    | cons u v => cons (Fhom F u) (map v)
    end.
  Lemma eval_map {A B} (u: hom_list A B) : eval (map u) ≡ Fhom F (eval u).
  Proof.
    elim: u=>[/=|C D f u IH]; simpl map. by rewrite Fidmap.
    by rewrite 2!eval_cons IH Fcomp.
  Qed.
    
  Program Definition r_Fhom {A B} (f: reified A B) :=
    reify (Fhom F f) (map (norm f)) _.
  Next Obligation. intros. by rewrite eval_map normE. Qed.  
  End s.
End HL.
Canonical HL.r_Fhom.


(** identity functor *)
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreFunctor.Build 𝐂 𝐂 idfun (fun A B => types_id).
HB.instance Definition _ (𝐂: PreCat) :=
  IsFunctor.Build 𝐂 𝐂 idfun (fun=> eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(** composition of functors *)
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: BarePreFunctor 𝐂 𝐃} {G: BarePreFunctor 𝐃 𝐄} :=
  IsBarePreFunctor.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom F)).
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: PreFunctor 𝐂 𝐃} {G: PreFunctor 𝐃 𝐄} :=
  IsPreFunctor.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom F)).
Program Definition _comp_functor 𝐂 𝐃 𝐄 {F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  IsFunctor.Build 𝐂 𝐄 (catcomp F G) _ _.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fidmap. Qed.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fcomp. Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_comp_functor 𝐂 𝐃 𝐄 F G.

(** constant functor *)
Definition cst {𝐂 𝐃: BareQuiver} (D: ob 𝐃) := fun of 𝐂 => D.
HB.instance Definition _ {𝐂: BareQuiver} {𝐃: BarePreCat} (D: 𝐃) :=
  IsBarePreFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (D: 𝐃) :=
  IsPreFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) :=
  IsFunctor.Build 𝐂 𝐃 (cst D) (fun=> eqv_refl)
    (fun _ _ _ _ _ => eqv_sym _ _ (compo1 idmap)).

Section s.
  Context {𝐂: PreCat} {𝐃: Cat} (F: Functor 𝐂 𝐃) (A B: ob 𝐂).
  Program Definition _functor_splitmono (i: SplitMono A B) := @HasRightInverse.Build _ _ _ (Fhom F i) (Fhom F (i⁻¹)) _.
  Next Obligation. intros. by rewrite -Fcomp invKr Fidmap. Qed.
  HB.instance Definition _ i := @_functor_splitmono i.
  Program Definition _functor_splitepi (i: SplitEpi A B) := @HasLeftInverse.Build _ _ _ (Fhom F i) (Fhom F (i⁻¹)) _.
  Next Obligation. intros. by rewrite -Fcomp invKl Fidmap. Qed.
  HB.instance Definition _ i := @_functor_splitepi i.
  HB.saturate Fhom.
  Check fun (i: A ≃ B) => Fhom F i: Iso _ _. 
End s.

(* waiting for universe polymorphism, we cannot declare the following instance *)
(* Unset Universe Checking. *)
(*TMP-UNIV
HB.instance Definition _ := IsBareQuiver.Build Cat Functor. 
*)
(* meanwhile, we use the following notation for functors; later we will replace it with "~>" *)
Notation "F ≈> G" := (Functor F G): cat_scope.
Definition functor_id {𝐂: PreCat}: 𝐂 ≈> 𝐂 := idfun: Functor 𝐂 𝐂.
Definition functor_comp {𝐂 𝐃 𝐄: PreCat} (F: 𝐂 ≈> 𝐃) (G: 𝐃 ≈> 𝐄): 𝐂 ≈> 𝐄 := catcomp F G: Functor _ _.
Definition functor_cst {𝐂} {𝐃: Cat} (D: 𝐃): 𝐂 ≈> 𝐃 := cst D: Functor _ _.
(*TMP-UNIV
HB.instance Definition _ := IsPreCat.Build Cat (@functor_id) (@functor_comp). 
*)

(** projections functors *)
HB.instance Definition _ (𝐂 𝐃: BareQuiver) := IsBarePreFunctor.Build (𝐂∧𝐃) 𝐂 fst (fun _ _ => fst).
HB.instance Definition _ (𝐂 𝐃: Quiver) := IsPreFunctor'.Build (𝐂∧𝐃) 𝐂 fst (fun _ _ _ _ => fst).
Lemma _fst_functor (𝐂 𝐃: PreCat): IsFunctor (𝐂∧𝐃) 𝐂 fst.
Proof. split; done. Qed.
HB.instance Definition _ 𝐂 𝐃 := @_fst_functor 𝐂 𝐃.

HB.instance Definition _ (𝐂 𝐃: BareQuiver) := IsBarePreFunctor.Build (𝐂∧𝐃) 𝐃 snd (fun _ _ => snd).
HB.instance Definition _ (𝐂 𝐃: Quiver) := IsPreFunctor'.Build (𝐂∧𝐃) 𝐃 snd (fun _ _ _ _ => snd).
Lemma _snd_functor (𝐂 𝐃: PreCat): IsFunctor (𝐂∧𝐃) 𝐃 snd.
Proof. split; done. Qed.
HB.instance Definition _ 𝐂 𝐃 := @_snd_functor 𝐂 𝐃.

HB.instance Definition _ I (𝐂: I -> BareQuiver) i := IsBarePreFunctor.Build (forall i, 𝐂 i) (𝐂 i) (app i) (fun _ _ => app i).
HB.instance Definition _ I (𝐂: I -> Quiver) i := IsPreFunctor'.Build (forall i, 𝐂 i) (𝐂 i) (app i) (fun _ _ _ _ => app i).
Lemma _app_functor I (𝐂: I -> PreCat) i: IsFunctor (forall i, 𝐂 i) (𝐂 i) (app i).
Proof. split; done. Qed.
HB.instance Definition _ I 𝐂 i := @_app_functor I 𝐂 i.


(** * Natural transformations *)

(** tranformations *)
Definition TX {𝐂: Type} {𝐃: BareQuiver} (F G: ob 𝐂 -> ob 𝐃) := forall X, F X ~> G X.
Identity Coercion TX_app: TX >-> Funclass.

(** naturality *)
#[primitive] HB.mixin Record IsNatural {𝐂: BareQuiver} {𝐃: PreCat} (F G: BarePreFunctor 𝐂 𝐃) (n: TX F G) :=
  { #[canonical=no] natural: forall (X Y: ob 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X }.
#[short(type="NTX")]
HB.structure Definition NATURAL 𝐂 𝐃 F G :=
  { n of @IsNatural 𝐂 𝐃 F G n }.
Arguments natural {_ _ _ _} _ [_ _] _.
Definition mk_ntx {𝐂: BareQuiver} {𝐃: PreCat} (F G: BarePreFunctor 𝐂 𝐃)
  (n: TX F G) (H: forall (X Y: ob 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X)
  := HB.pack_for (NTX F G) n (IsNatural.Build _ _ F G n H).
Arguments mk_ntx {_ _} _ _ _ _.

(** duality *)
Definition ntxop {𝐂 𝐃 F G} (n: @TX 𝐂 𝐃 F G): TX (funcop G) (funcop F) := n. 
Definition ntxop' {𝐂 𝐃 F G} (n: TX F G): @TX 𝐂 𝐃 (funcop' G) (funcop' F) := n.

HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor 𝐂 𝐃) (n: NTX F G) :=
  IsNatural.Build _ _ _ _ (ntxop n) (fun _ _ _ => eqv_sym _ _ (natural n _)).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor _ _) (n: NTX F G) :=
  IsNatural.Build 𝐂 𝐃 _ _ (ntxop' n) (fun _ _ _ => eqv_sym _ _ (natural n _)).

Definition ntxop12 {𝐂 𝐃 F G} (n: @TX _ 𝐃 F G): @TX 𝐂 _ (funcop12 G) (funcop12 F) := n. 
Definition ntxop21 {𝐂 𝐃 F G} (n: @TX 𝐂 _ F G): @TX _ 𝐃 (funcop21 G) (funcop21 F) := n.

HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor _ 𝐃) (n: NTX F G) :=
  IsNatural.Build 𝐂 _ _ _ (ntxop12 n) (fun _ _ _ => eqv_sym _ _ (natural n _)).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor 𝐂 _) (n: NTX F G) :=
  IsNatural.Build _ 𝐃 _ _ (ntxop21 n) (fun _ _ _ => eqv_sym _ _ (natural n _)).


(** setoid structure on natural transformations *)
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor 𝐂 𝐃) :=
  Setoid.copy (NTX F G) (kernel (@NATURAL.sort 𝐂 𝐃 F G)).

(** ** categories of (pre)functors and natural transformations *)
HB.instance Definition _  𝐂 (𝐃: PreCat) :=
  IsQuiver.Build (PreFunctor 𝐂 𝐃) (@NTX 𝐂 𝐃).
HB.instance Definition _  𝐂 𝐃 :=
  IsQuiver.Build (Functor 𝐂 𝐃) (@NTX 𝐂 𝐃).

Definition ntx_id_ 𝐂 {𝐃: PreCat} (F: BarePreFunctor 𝐂 𝐃): TX F F :=
  fun X => idmap (F X).
Arguments ntx_id_ {_ _} _ _ /. 
Lemma _ntx_id_natural 𝐂 (𝐃: Cat) (F: BarePreFunctor 𝐂 𝐃):
  IsNatural 𝐂 𝐃 F F (ntx_id_ F).
Proof. constructor=>X Y f/=. cat. Qed.
HB.instance Definition _ 𝐂 𝐃 F := @_ntx_id_natural 𝐂 𝐃 F.
Definition pre_ntx_id {𝐂} {𝐃: Cat} (F: PreFunctor 𝐂 𝐃): F ~> F := (ntx_id_ F: NTX _ _). 
Definition ntx_id {𝐂} {𝐃: Cat} (F: Functor 𝐂 𝐃): F ~> F := (ntx_id_ F: NTX _ _). 

Definition ntx_comp_ {𝐂} {𝐃: PreCat} (F G H: BarePreFunctor 𝐂 𝐃) (m: TX F G) (n: TX G H): TX F H :=
  fun X => n X ∘ m X.
Arguments ntx_comp_ {_ _ _ _ _} _ _ _/. 
Lemma _ntx_comp_natural 𝐂 (𝐃: Cat) (F G H: PreFunctor 𝐂 𝐃) (m: F ~> G) (n: G ~> H) :
  IsNatural 𝐂 𝐃 F H (@ntx_comp_ 𝐂 𝐃 F G H m n).
Proof.
  constructor=>A B f /=.
  by rewrite -compoA natural compoA natural compoA.
Qed.
HB.instance Definition _ 𝐂 𝐃 F G H m n := @_ntx_comp_natural 𝐂 𝐃 F G H m n.
Definition pre_ntx_comp {𝐂} {𝐃: Cat} (F G H: PreFunctor 𝐂 𝐃) (n: F ~> G) (m: G ~> H): F ~> H :=
  (ntx_comp_ n m: NTX _ _). 
Definition ntx_comp {𝐂} {𝐃: Cat} (F G H: Functor 𝐂 𝐃) (n: F ~> G) (m: G ~> H): F ~> H :=
  (ntx_comp_ n m: NTX _ _). 

HB.instance Definition _ 𝐂 (𝐃: Cat) :=
  IsPreCat.Build (PreFunctor 𝐂 𝐃) pre_ntx_id pre_ntx_comp.
HB.instance Definition _ 𝐂 (𝐃: Cat) :=
  IsPreCat.Build (Functor 𝐂 𝐃) ntx_id ntx_comp.

Lemma _prefunctor_cat 𝐂 (𝐃: Cat): IsCat (PreFunctor 𝐂 𝐃).
Proof.
  constructor; repeat intro. 
  - exact: comp1o. 
  - exact: compo1. 
  - exact: compoA. 
  - exact: comp_eqv.
Qed.
HB.instance Definition _ 𝐂 𝐃 := _prefunctor_cat 𝐂 𝐃.

(* TODO with faithful subcat ? *)
Lemma _functor_cat 𝐂 (𝐃: Cat): IsCat (Functor 𝐂 𝐃).
Proof.
  constructor; repeat intro.
  - exact: comp1o.
  - exact: compo1.
  - exact: compoA.
  - exact: comp_eqv.
Qed.
HB.instance Definition _ 𝐂 𝐃 := _functor_cat 𝐂 𝐃.

(* Check fun (𝐂: Cat) (F: Functor 𝐂 𝐂) (f: F ~> F) => let G: PreFunctor _ _ := F in f: G ~> G. *)

Definition ntx_comp'_ 𝐂 𝐃 {𝐄: PreCat} {F G: BarePreFunctor 𝐂 𝐃} {F' G': BarePreFunctor 𝐃 𝐄}
  (k: TX F G) (h: TX F' G'): TX (catcomp F F') (catcomp G G') :=
  (fun X => h _ ∘ Fhom _ (k _)).
Arguments ntx_comp'_ {_ _ _ _ _ _ _} _ _ _/. 
Program Definition _ntx_comp'_natural 𝐂 𝐃 (𝐄: Cat) (F G: 𝐂 ≈> 𝐃) (F' G': 𝐃 ≈> 𝐄)
  (k: F ~> G) (h: F' ~> G') := IsNatural.Build 𝐂 𝐄 (catcomp F F') (catcomp G G') (ntx_comp'_ k h) _.
Next Obligation.
  intros. cbn. 
  rewrite natural -compoA !natural.
  rewrite compoA -Fcomp natural.
  Fail cat.                     (* was working before *)
  rewrite !Fcomp. cat. 
Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G F' G' k h := @_ntx_comp'_natural 𝐂 𝐃 𝐄 F G F' G' k h.
Definition ntx_comp' {𝐂 𝐃 𝐄: Cat} {F G: 𝐂 ≈> 𝐃} {F' G': 𝐃 ≈> 𝐄}
  (*TMP-UNIV: functor_comp -> ∘ once we have Cat:Cat  *)
  (n: F ~> G) (m: F' ~> G'): (functor_comp F F') ~> (functor_comp G G') :=
  (ntx_comp'_ n m: NTX _ _). 
Notation "h ⊚ k" := (ntx_comp' k h): cat_scope. (* TODO: reverse this notation! *)


(* TODO: un/currying  *)
(* HB.instance Definition _ (C D: Quiver) (E: PreCat) (F: PreFunctor (C∧D) E) := *)
(*   IsBarePreFunctor.Build C (PreFunctor D E) curry _.  *)



(** * duality [C->D]^op ≃ [C^op->D^op] *)

Section s.
Context {𝐂: PreCat} {𝐃: Cat}.
Definition opfunc (F: ob (Functor 𝐂 𝐃)^op): ob (Functor 𝐂^op 𝐃^op) := funcop F: Functor _ _.
Definition opfunc' (F: ob (Functor 𝐂^op 𝐃^op)): ob (Functor 𝐂 𝐃)^op := funcop' F: Functor _ _.

(* first two instances only need 𝐃: PreCat *)
HB.instance Definition _ :=
  IsBarePreFunctor.Build _ _ opfunc (fun _ _ n => ntxop n: NTX _ _).
HB.instance Definition _ :=
  IsPreFunctor'.Build _ _ opfunc (fun _ _ _ _ H => H).
HB.instance Definition _ :=
  IsFunctor.Build _ _ opfunc (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(* first two instances only need 𝐃: PreCat *)
HB.instance Definition _ :=
  IsBarePreFunctor.Build _ _ opfunc' (fun _ _ n => ntxop' n: NTX _ _).
HB.instance Definition _ :=
  IsPreFunctor'.Build _ _ opfunc' (fun _ _ _ _ H => H).
HB.instance Definition _ :=
  IsFunctor.Build _ _ opfunc' (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(* TODO: actually an adjoint equivalence *)

Definition opfunc12 (F: ob (Functor 𝐂^op 𝐃)^op): ob (Functor 𝐂 𝐃^op) := funcop12 F: Functor _ _.
Definition opfunc12' (F: ob (Functor 𝐂 𝐃^op)): ob (Functor 𝐂^op 𝐃)^op := funcop21 F: Functor _ _.

(* first two instances only need 𝐃: PreCat *)
HB.instance Definition _ :=
  IsBarePreFunctor.Build _ _ opfunc12 (fun _ _ n => ntxop12 n: NTX _ _).
HB.instance Definition _ :=
  IsPreFunctor'.Build _ _ opfunc12 (fun _ _ _ _ H => H).
HB.instance Definition _ :=
  IsFunctor.Build _ _ opfunc12 (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(* first two instances only need 𝐃: PreCat *)
HB.instance Definition _ :=
  IsBarePreFunctor.Build _ _ opfunc12' (fun _ _ n => ntxop21 n: NTX _ _).
HB.instance Definition _ :=
  IsPreFunctor'.Build _ _ opfunc12' (fun _ _ _ _ H => H).
HB.instance Definition _ :=
  IsFunctor.Build _ _ opfunc12' (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(* TODO: actually an adjoint equivalence *)

Definition opfunc21 (F: ob (Functor 𝐂 𝐃^op)^op): ob (Functor 𝐂^op 𝐃) := funcop21 F: Functor _ _.
Definition opfunc21' (F: ob (Functor 𝐂^op 𝐃)): ob (Functor 𝐂 𝐃^op)^op := funcop12 F: Functor _ _.

(* first two instances only need 𝐃: PreCat *)
HB.instance Definition _ :=
  IsBarePreFunctor.Build _ _ opfunc21 (fun _ _ n => ntxop21 n: NTX _ _).
HB.instance Definition _ :=
  IsPreFunctor'.Build _ _ opfunc21 (fun _ _ _ _ H => H).
HB.instance Definition _ :=
  IsFunctor.Build _ _ opfunc21 (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(* first two instances only need 𝐃: PreCat *)
HB.instance Definition _ :=
  IsBarePreFunctor.Build _ _ opfunc21' (fun _ _ n => ntxop12 n: NTX _ _).
HB.instance Definition _ :=
  IsPreFunctor'.Build _ _ opfunc21' (fun _ _ _ _ H => H).
HB.instance Definition _ :=
  IsFunctor.Build _ _ opfunc21' (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(* TODO: actually an adjoint equivalence *)

End s. 


(** * adjunctions *)

(** ** functions with an adjoint candidate *)

#[primitive] 
HB.mixin Record IsPreAdjoint {𝐂 𝐃: Type} (F: ob 𝐂 -> ob 𝐃) :=
  { #[canonical=no] adj: ob 𝐃 -> ob 𝐂 }.
#[short(type="PreAdjoint")]
HB.structure Definition PREADJOINT 𝐂 𝐃 := {F of IsPreAdjoint 𝐂 𝐃 F & }.
Arguments adj {_ _}.

HB.instance Definition _ {𝐂 𝐃: Type} (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐃 𝐂 (adj F) F.

HB.instance Definition _ {𝐂 𝐃: Type} (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐂^op 𝐃^op (funcop F) (funcop (adj F)).
HB.instance Definition _ {𝐂 𝐃: Type} (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐂^op 𝐃 (funcop12 F) (funcop21 (adj F)).
HB.instance Definition _ {𝐂 𝐃: Type} (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐂 𝐃^op (funcop21 F) (funcop12 (adj F)).

HB.instance Definition _ {𝐂: Type} := IsPreAdjoint.Build 𝐂 𝐂 idfun idfun.
HB.instance Definition _ {𝐂: BareQuiver} := IsPreAdjoint.Build 𝐂 𝐂^op obop obop'.
HB.instance Definition _ {𝐂: BareQuiver} := IsPreAdjoint.Build 𝐂^op 𝐂 obop' obop.
HB.instance Definition _ {𝐂 𝐃 𝐄: Type} (F: PreAdjoint 𝐂 𝐃) (G: PreAdjoint 𝐃 𝐄) :=
  IsPreAdjoint.Build 𝐂 𝐄 (catcomp F G) (catcomp (adj G) (adj F)).

(** ** functors with an adjoint candidate *)

#[primitive] 
HB.mixin Record IsPreAdjointF {𝐂 𝐃: PreCat} F of @PREADJOINT 𝐂 𝐃 F :=
  { #[canonical=no] _adj_functor: @FUNCTOR.axioms_ _ _ (adj F) }.
#[short(type="PreAdjointF")]
HB.structure Definition PREADJOINTF 𝐂 𝐃 := {F of @FUNCTOR 𝐂 𝐃 F & IsPreAdjointF _ _ F & IsPreAdjoint _ _ F}.
HB.instance Definition _ 𝐂 𝐃 F := @_adj_functor 𝐂 𝐃 F. 

HB.factory Record IsPreAdjointF' 𝐂 𝐃 F of @FUNCTOR 𝐂 𝐃 F :=
  { adj: Functor 𝐃 𝐂 }.
HB.builders Context 𝐂 𝐃 F of IsPreAdjointF' 𝐂 𝐃 F. 
  HB.instance Definition _ := IsPreAdjoint.Build 𝐂 𝐃 F adj. 
  HB.instance Definition _ := IsPreAdjointF.Build 𝐂 𝐃 F (FUNCTOR.class adj).
HB.end.

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointF'.Build 𝐃 𝐂 (adj F) F.

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointF'.Build _ _ (funcop F) (funcop (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF _ _) :=
  IsPreAdjointF'.Build 𝐂 𝐃 (funcop' F) (funcop' (adj F)).

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF _ 𝐃) :=
  IsPreAdjointF'.Build 𝐂 _ (funcop12 F) (funcop21 (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 _) :=
  IsPreAdjointF'.Build _ 𝐃 (funcop21 F) (funcop12 (adj F)).

HB.instance Definition _ 𝐂 := IsPreAdjointF'.Build 𝐂 𝐂 idfun idfun.

HB.instance Definition _ 𝐂 𝐃 𝐄 (F: PreAdjointF 𝐂 𝐃) (G: PreAdjointF 𝐃 𝐄) :=
  IsPreAdjointF'.Build 𝐂 𝐄 (catcomp F G) (catcomp (adj G) (adj F)).



(** ** adjunctions *)
(** first without HB *)
Module Adj.
Definition type {𝐂 𝐃: PreCat} (F: PreFunctor 𝐂 𝐃) (G: PreFunctor 𝐃 𝐂) :=
  { unit: NTX idfun (catcomp F G) &
  { counit: NTX (catcomp G F) idfun |
  (* { unit: functor_id ~> functor_comp F G & *)
  (* { counit: functor_comp G F ~> functor_id | *)
    (forall A, Fhom F (unit A) \; counit (F A) ≡ F A)
  /\ (forall B, unit (G B) \; Fhom G (counit B) ≡ G B) 
    (* unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _; *)
    (* unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _; *)
  }}.
Section s.
Context {𝐂 𝐃 F G} (a: @type 𝐂 𝐃 F G).
Definition mk
  (unit: NTX idfun (catcomp F G)) (counit: NTX (catcomp G F) idfun)
  (H1: forall A, Fhom F (unit A) \; counit (F A) ≡ F A)
  (H2: forall B, unit (G B) \; Fhom G (counit B) ≡ G B): type F G :=
  existT _ unit (exist _ counit (conj H1 H2)).
Definition unit: NTX idfun (catcomp F G) := projT1 a.
Definition counit: NTX (catcomp G F) idfun := proj1_sig (projT2 a).
Definition unit_counit_l_at: forall A, Fhom F (unit A) \; counit (F A) ≡ F A := proj1 (proj2_sig (projT2 a)).
Definition unit_counit_r_at: forall B, unit (G B) \; Fhom G (counit B) ≡ G B := proj2 (proj2_sig (projT2 a)).
End s.
Arguments mk {_ _ _ _} & .
Section s.
Context {𝐂 𝐃: Cat} {F G: Functor _ _} (a: @type 𝐂 𝐃 F G).
Definition unit': functor_id ~> functor_comp F G := unit a. (* abbreviation? *)
Definition counit': functor_comp G F ~> functor_id := counit a. (* abbreviation? *)
Lemma unit_counit_l: idmap ⊚ unit a \; counit a ⊚ idmap ≡ ntx_id _.
Proof. move=>A. move:(unit_counit_l_at a A)=>/=. by rewrite !cats. Qed.
Lemma unit_counit_r: unit a ⊚ idmap \; idmap ⊚ counit a ≡ ntx_id _.
Proof. move=>B. move:(unit_counit_r_at a B)=>/=. by rewrite !cats. Qed.
End s.

Program Definition id {𝐂: Cat}: @type 𝐂 𝐂 idfun idfun :=
  mk (ntx_id _) (ntx_id _) _ _.
Next Obligation. cbn=>*. cat. Qed.
Next Obligation. cbn=>*. cat. Qed.

Program Definition comp {𝐂 𝐃 𝐄: Cat} {F F' G G': Functor _ _}
  (FF: @type 𝐂 𝐃 F F')
  (GG: @type 𝐃 𝐄 G G'):
  type (catcomp F G) (catcomp G' F') :=
  mk
    (unit' FF \; idmap ⊚ unit' GG ⊚ idmap)
    (idmap ⊚ counit' FF ⊚ idmap \; counit' GG) _ _.
Admit Obligations.
(* Next Obligation. move=>𝐂 𝐃 𝐄 F F' G G' FF GG A/=. rewrite !cats. Admitted.  *)
(* Next Obligation. move=>𝐂 𝐃 𝐄 F F' G G' FF GG B/=. rewrite !cats. Admitted.  *)

Definition op {𝐂 𝐃 F G}
  (FG: @type 𝐂 𝐃 F G):
  type (funcop G) (funcop F) :=
  mk
    (ntxop (counit FG): NTX _ _)
    (ntxop (unit FG): NTX _ _)
    (unit_counit_r_at FG)
    (unit_counit_l_at FG).

Definition op' {𝐂 𝐃} {F G: PreFunctor _ _}
  (FG: type F G):
  @type 𝐂 𝐃 (funcop' G) (funcop' F) :=
  mk
    (ntxop' (counit FG): NTX _ _)
    (ntxop' (unit FG): NTX _ _)
    (unit_counit_r_at FG)
    (unit_counit_l_at FG).

End Adj.


(** ** left adjoints (= functors with a right adjoint) *)

#[primitive] HB.mixin Record IsLeftAdjoint {𝐂 𝐃: PreCat} F of @PREADJOINTF 𝐂 𝐃 F :=
  { #[canonical=no] ladjP: Adj.type F (adj F) }.
#[short(type="LeftAdjoint")]
HB.structure Definition LEFTADJOINT 𝐂 𝐃 := {F of IsLeftAdjoint 𝐂 𝐃 F & }.
Infix "⊣" := LeftAdjoint (at level 79): cat_scope.
Section s.
Context {𝐂 𝐃} (F: 𝐂 ⊣ 𝐃).
Definition unit: NTX idfun (catcomp F (adj F)) := Adj.unit ladjP.
Definition counit: NTX (catcomp (adj F) F) idfun := Adj.counit ladjP.
Definition unit_counit_l_at: forall A, Fhom F (unit A) \; counit (F A) ≡ F A := Adj.unit_counit_l_at ladjP.
Definition unit_counit_r_at: forall B, unit (adj F B) \; Fhom (adj F) (counit B) ≡ adj F B := Adj.unit_counit_r_at ladjP.
End s.
Arguments unit {_ _ _}, {_ _} _.
Arguments counit {_ _ _}, {_ _} _.
Section s.
Context {𝐂 𝐃: Cat} (F: 𝐂 ⊣ 𝐃).
Definition unit_counit_l: idmap ⊚ unit F \; counit F ⊚ idmap ≡ ntx_id _ := Adj.unit_counit_l ladjP.
Definition unit_counit_r: unit F ⊚ idmap \; idmap ⊚ counit F ≡ ntx_id _ := Adj.unit_counit_r ladjP.
End s.


(** ** right adjoints (= functors with a left adjoint) *)

#[primitive] HB.mixin Record IsRightAdjoint {𝐂 𝐃: PreCat} F of @PREADJOINTF 𝐂 𝐃 F :=
  { #[canonical=no] radjP: Adj.type (adj F) F }.
#[short(type="RightAdjoint")]
HB.structure Definition RIGHTADJOINT 𝐂 𝐃 := {F of IsRightAdjoint 𝐂 𝐃 F & }.
Infix "⊢" := RightAdjoint (at level 79): cat_scope.
Section s.
Context {𝐂 𝐃} (F: 𝐂 ⊢ 𝐃).
Definition unit': NTX idfun (catcomp (adj F) F) := Adj.unit radjP.
Definition counit': NTX (catcomp F (adj F)) idfun := Adj.counit radjP.
Definition unit_counit_l_at': forall A, Fhom (adj F) (unit' A) \; counit' (adj F A) ≡ adj F A := Adj.unit_counit_l_at radjP.
Definition unit_counit_r_at': forall B, unit' (F B) \; Fhom F (counit' B) ≡ F B := Adj.unit_counit_r_at radjP.
End s.
Arguments unit' {_ _ _}, {_ _} _.
Arguments counit' {_ _ _}, {_ _} _.
Section s.
Context {𝐂 𝐃: Cat} (F: 𝐂 ⊢ 𝐃).
Definition unit_counit_l': idmap ⊚ unit' F \; counit' F ⊚ idmap ≡ ntx_id _ := Adj.unit_counit_l radjP.
Definition unit_counit_r': unit' F ⊚ idmap \; idmap ⊚ counit' F ≡ ntx_id _ := Adj.unit_counit_r radjP.
End s.

(** ** adjoint equivalences (= functors which are both left and right adjoints) *)

#[short(type="AdjointEquivalence")]
HB.structure Definition ADJOINTEQUIVALENCE 𝐂 𝐃 :=
  {F of @LEFTADJOINT 𝐂 𝐃 F & @RIGHTADJOINT 𝐂 𝐃 F }.



(** * adjunction instances *)

(** ** duality instances *)

(* LA <-adj-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊣ 𝐃) :=
  IsRightAdjoint.Build 𝐃 𝐂 (adj F) ladjP.
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊢ 𝐃) :=
  IsLeftAdjoint.Build 𝐃 𝐂 (adj F) radjP.

(* LA <-funcop-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊣ 𝐃) :=
  IsRightAdjoint.Build _ _ (funcop F) (Adj.op ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊢ 𝐃) :=
  IsLeftAdjoint.Build _ _ (funcop F) (Adj.op ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: _ ⊣ _) :=
  IsRightAdjoint.Build 𝐂 𝐃 (funcop' F) (Adj.op' ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: _ ⊢ _) :=
  IsLeftAdjoint.Build 𝐂 𝐃 (funcop' F) (Adj.op' ladjP).

(** ** identity adjunctions *)
HB.instance Definition _ (𝐂: Cat) := IsLeftAdjoint.Build 𝐂 𝐂 idfun Adj.id.
HB.instance Definition _ (𝐂: Cat) := IsRightAdjoint.Build 𝐂 𝐂 idfun Adj.id.

(** ** composing adjunctions  *)
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: LeftAdjoint 𝐂 𝐃) (G: LeftAdjoint 𝐃 𝐄) :=
  IsLeftAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp ladjP ladjP).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: RightAdjoint 𝐂 𝐃) (G: RightAdjoint 𝐃 𝐄) :=
  IsRightAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp radjP radjP).


(* TOFIX: declarations below are no-ops *)
HB.saturate adj. 
HB.saturate funcop. 
HB.saturate catcomp. 
(* we emulate them using the following asymmetric declarations *)
HB.instance Definition _ C D (F: AdjointEquivalence C D) := LEFTADJOINT.on (adj F).
HB.instance Definition _ C D (F: AdjointEquivalence C D) := LEFTADJOINT.on (funcop F).
HB.instance Definition _ (C D E: Cat) (F: AdjointEquivalence C D) (G: AdjointEquivalence D E) := LEFTADJOINT.on (catcomp F G).

Check fun (C D: Cat) (F: AdjointEquivalence C D) => adj F: AdjointEquivalence D C. 
Check fun (C D: Cat) (F: AdjointEquivalence C D) => funcop F: AdjointEquivalence (C^op) (D^op). 
Check fun (C: Cat) (F G: AdjointEquivalence C C) => catcomp F G: AdjointEquivalence C C. 


(** * additional factories *)
HB.factory Record IsAdjointEquivalence {𝐂 𝐃: Cat} F of @PREADJOINTF 𝐂 𝐃 F :=
  { adjKl: functor_comp (adj F) F ≃ functor_id;
    adjKr: functor_comp F (adj F) ≃ functor_id;
    unit_counit_l_at: forall A, Fhom F (adjKr⁻¹ A) \; adjKl¹ (F A) ≡ F A;
    unit_counit_r_at: forall B, adjKr⁻¹ (adj F B) \; Fhom (adj F) (adjKl¹ B) ≡ adj F B;
    (* unit_counit_l: idmap ⊚ adjKr⁻¹ \; adjKl ⊚ idmap ≡ ntx_id _; *)
    (* unit_counit_r: adjKr⁻¹ ⊚ idmap \; idmap ⊚ adjKl ≡ ntx_id _; *)
  }.
HB.builders Context 𝐂 𝐃 F of @IsAdjointEquivalence 𝐂 𝐃 F.
HB.instance Definition _ :=
  @IsLeftAdjoint.Build 𝐂 𝐃 F (Adj.mk adjKr⁻¹ adjKl¹ unit_counit_l_at unit_counit_r_at).  
(* TODO&MOVE to module Adj *)
Lemma unit_counit_l_at': forall A, Fhom (adj F) (adjKl⁻¹ A) \; adjKr¹ (adj F A) ≡ adj F A. Admitted.
Lemma unit_counit_r_at': forall B, adjKl⁻¹ (F B) \; Fhom F (adjKr¹ B) ≡ F B. Admitted.
HB.instance Definition _ :=
  @IsRightAdjoint.Build 𝐂 𝐃 F (Adj.mk adjKl⁻¹ adjKr¹ unit_counit_l_at' unit_counit_r_at').  
HB.end.



(** * theory of left adjunctions *)
Section theory.
Context {𝐂 𝐃: Cat} (F: 𝐂 ⊣ 𝐃).

Definition up {A B} (f: F A ~> B): A ~> adj F B :=
  Fhom (adj F) f ∘ unit F A.
Definition dn {A B} (f: A ~> adj F B): F A ~> B :=
  counit F B ∘ Fhom F f. 

Lemma up_eqv {A B}: Proper (eqv ==> eqv) (@up A B).
Proof. move=>f f' ff. rewrite/up. apply:comp_eqv=>//. exact/Fhom_eqv. Qed.
HB.instance Definition _ A B := isExtensional.Build _ _ _ (@up_eqv A B). 

Lemma dn_eqv {A B}: Proper (eqv ==> eqv) (@dn A B).
Proof. move=>f f' ff. rewrite/dn. apply:comp_eqv=>//. exact/Fhom_eqv. Qed.
HB.instance Definition _ A B := isExtensional.Build _ _ _ (@dn_eqv A B). 

Lemma dn_up {A B} (f: F A ~> B): dn (up f) ≡ f.
Proof.
  rewrite /dn/up/=Fcomp.
  arewrite (natural counit). 
  arewrite (unit_counit_l_at F).
  cat. 
Qed.

Lemma up_inj {A B}: injective (@up A B).
Proof. move=>f g H. rewrite -(dn_up f) -(dn_up g). exact/dn_eqv. Qed.

Lemma up_dn {A B} (f: A ~> adj F B): up (dn f) ≡ f.
Proof.
  rewrite /dn/up/=Fcomp.
  arewrite -(natural unit). 
  arewrite (unit_counit_r_at F).
  cat. 
Qed.

Lemma dn_inj {A B} (f f': A ~> adj F B): dn f ≡ dn f' -> f ≡ f'.
Proof. move=>H. rewrite -(up_dn f) -(up_dn f'). exact/up_eqv. Qed.

(** left adjoints preserve initial objects *)
Theorem ladj_initial (A: ob 𝐂) (H: initial A): initial (F A).
Proof. move=>X. apply: (unique_impl dn up_inj). exact/H. Defined.

End theory.

Lemma radj_terminal (𝐂 𝐃: Cat) (F: 𝐂 ⊢ 𝐃) (A: ob 𝐂) (H: terminal A): terminal (F A).
Proof. exact: (ladj_initial (funcop F) H). Defined.
(* TOTHINK: forgetful inheritance wrongly detected?
   (should be fine because this is about two distinct hierarchies:
    - the one for functors (indexed by functions [ob C -> ob D]
    - and the one for objects (indexed by objects [ob C]
    is this the source of confusion? )
 *)
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: 𝐂 ⊣ 𝐃) (A: Initial 𝐂) :=
  IsInitial.Build 𝐃 (F A) (ladj_initial F initialP).
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: 𝐂 ⊢ 𝐃) (A: Terminal 𝐂) :=
  IsTerminal.Build 𝐃 (F A) (radj_terminal F terminalP).

Check fun (𝐂 𝐃: Cat) (F: 𝐂 ⊢ 𝐃) (A: Terminal 𝐂) => F A: Terminal _.
(* TOFIX: HB does not register the required things...
   use a tag above to adhere to its discipline? *)
Fail Check fun (𝐂 𝐃: Cat) (F: AdjointEquivalence 𝐂 𝐃) (A: Terminal 𝐂) => F A: Terminal _.



(** ** functor equivalence (i.e., natural isomorphisms) *)

Section s.
Context {𝐂} {𝐃: Cat} (F G: Functor 𝐂 𝐃).
Definition functor_equiv := F ≃ G.

(** alternative constructors for natural isomorphisms  *)
Program Definition iso_ntx'
  (i: forall X, F X ≃ G X) (n: F ~> G)
  (H: forall X, n X ≡ i X): functor_equiv :=
  iso_ n (mk_ntx G F (fun X => (i X)⁻¹) _) _ _.
Next Obligation.
  intros=>/=. rewrite -iso_src.
  rewrite -H -compoA -natural.
  by rewrite compoA H invKr cats. 
Qed.
Next Obligation. cbn=>i n H A/=. by rewrite H invKl. Qed.
Next Obligation. cbn=>i n H A/=. by rewrite H invKr. Qed.

(** via natural tranformations which are pointwise isomorphisms *)
Definition iso_ntx
  (i: forall X, F X ≃ G X):
  (forall X Y h, i Y ∘ Fhom F h ≡ Fhom G h ∘ i X) -> functor_equiv.
Proof. move=>N. exact: (@iso_ntx' i (mk_ntx _ _ i N)). Defined.

(** when the functors actually are pointwise equal *)
Lemma same_functor
  (FG1: forall X, F X = G X)
  (FG2: forall (A B: ob 𝐂) (f: A ~> B), Fhom G f ≡ cast2' (T:=hom) (Fhom F f) (FG1 A) (FG1 B)):
  functor_equiv.
Proof.
  unshelve apply: iso_ntx.
  - intro. rewrite FG1. exact: iso_refl.
  - intros A B f. rewrite /= FG2 /cast2' /=.
    destruct (FG1 A); destruct (FG1 B).
    by simpl; cat. 
Defined.

(** natural isomorphisms pointwise yield isomorphisms *)
Definition iso_ntx_pw (i: functor_equiv) X: F X ≃ G X :=
  iso_ (i¹ X) (i⁻¹ X) (invKl i X) (invKr i X). 

(* Definition iso_ntx_pw_ (i: functor_equiv): forall X, F X ~> G X := fun X => (i¹ X). *)
(* HB.instance Definition _ (i: functor_equiv) X := *)
(*   IsIso.Build _ _ _ (iso_ntx_pw_ i X) (invKl i X) (invKr i X). *)
(* Definition iso_ntx_pw (i: functor_equiv) X: F X ≃ G X := iso_ntx_pw_ i X.  *)

End s.
Coercion iso_ntx_pw: functor_equiv >-> Funclass.
Infix "≈" := functor_equiv: cat_scope.

(* Check fun {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃) (i: F ≈ G) (X: 𝐂) => unify (i⁻¹ X)  (i X)⁻¹. *)

Lemma iso_ntx_alt 𝐂 (𝐃: Cat) (F G: 𝐂 ≈> 𝐃) (i: F ≈ G) A B (f: A ~> B):
  Fhom G f ≡ i B ∘ Fhom F f ∘ (i A)⁻¹.
Proof. rewrite natural -compoA invKl. cat. Qed.

Lemma iso_ntx_eqv 𝐂 (𝐃: Cat) (F G: 𝐂 ≈> 𝐃) (i: F ≈ G) A B (f g: A ~> B):
  Fhom F f ≡ Fhom F g -> Fhom G f ≡ Fhom G g.
Proof. rewrite 2!(iso_ntx_alt i). by move=>->. Qed.

(* Check fun {𝐂 𝐃: Cat} (F G: 𝐂 ≈> 𝐃) (i: F ≈ G) (X: 𝐂) => unify (i⁻¹ X)  (i X)⁻¹. *)

Section strict.
Context {𝐂 𝐃 𝐄: Cat}.
Lemma endo_exchange {F G H: 𝐂 ≈> 𝐃} {F' G' H': 𝐃 ≈> 𝐄}
  (i: F ~> G) (j: G ~> H)
  (i': F' ~> G') (j': G' ~> H'):
  (j'⊚j) ∘ (i'⊚i) ≡ (j'∘i') ⊚ (j∘i).
Proof.
  intro X; cbn.
  rewrite -!compoA. apply: comp_eqv=>//.
  normalise. by rewrite natural.
Qed.

Lemma ntx_id_comp {F: 𝐂 ≈> 𝐃} {G: 𝐃 ≈> 𝐄}:
  (*TMP-UNIV: functor_comp -> ∘ once we have Cat:Cat  *)
  idmap (functor_comp F G) ≡ idmap G ⊚ idmap F.
Proof. intro X; cbn. by rewrite !cats. Qed.

Lemma ntx_comp'_eqv {F G: 𝐂 ≈> 𝐃} {F' G': 𝐃 ≈> 𝐄}:
  Proper (eqv ==> eqv ==> eqv) (@ntx_comp' _ _ _ F G F' G').
Proof.
  intros i i' ii j j' jj X=>/=.
  Fail by rewrite /= (ii _) (jj _).  (* FIXRW *)
  apply: comp_eqv. apply: Fhom_eqv. exact: ii. exact: jj. 
Qed.

Import CMorphisms.
Lemma functor_comp_iso:
  Proper (functor_equiv ==> functor_equiv ==> functor_equiv) (@functor_comp 𝐂 𝐃 𝐄).
Proof.
  intros F G i F' G' j. 
  apply: (iso_ (j⊚ i) (j⁻¹⊚i⁻¹) _ _).
  abstract (rewrite endo_exchange; etransitivity;
            [exact: (ntx_comp'_eqv (invKl i) (invKl j)) | by rewrite -ntx_id_comp]).
  abstract (rewrite endo_exchange; etransitivity;
            [exact: (ntx_comp'_eqv (invKr i) (invKr j)) | by rewrite -ntx_id_comp]).
Defined.
End strict.
