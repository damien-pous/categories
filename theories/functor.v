(** * Functors and natural transformations *)

Require Import cat morphisms.
Require Import arewrite.

Open Scope cat_scope.

(** * Functors *)

Definition FUN A B := ob A -> ob B.
Identity Coercion FUNfun: FUN >-> Funclass. 

(** ** diagrams: barequiver morphisms *)
#[primitive] HB.mixin Record IsDiagram (𝐂 𝐃: BareQuiver) (F: FUN 𝐂 𝐃) := {
   #[canonical=no] Fhom: forall a b: ob 𝐂, (a ~> b) -> (F a ~> F b);
  }.
#[short(type="Diagram")]
HB.structure Definition DIAGRAM 𝐂 𝐃 :=
  { F of IsDiagram 𝐂 𝐃 F }.
Arguments Fhom {_ _} _ {_ _}. 

(** ** prefunctors: quiver morphisms, i.e., functors without laws *)
#[primitive] HB.mixin Record Diagram_IsPreFunctor (𝐂 𝐃: Quiver) F of @DIAGRAM 𝐂 𝐃 F := {
   #[canonical=no] _Fhom_eqv: forall a b: ob 𝐂, Proper (eqv ==> eqv) (@Fhom _ _ F a b);
  }.
#[short(type="PreFunctor")]
HB.structure Definition PREFUNCTOR 𝐂 𝐃 :=
  { F of Diagram_IsPreFunctor 𝐂 𝐃 F & }.
Instance Fhom_eqv {𝐂 𝐃: Quiver} {F: PreFunctor 𝐂 𝐃} {a b: ob 𝐂}: Proper (eqv ==> eqv) (Fhom F) :=
  _Fhom_eqv a b. 
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) a b :=
  isExtensional.Build _ _ (@Fhom _ _ F a b) _. 

(** direct factory, for constructing prefunctors from scratch *)
HB.factory Record IsPreFunctor (𝐂 𝐃: Quiver) (F: FUN 𝐂 𝐃) := {
    Fhom: forall a b, (a ~> b) -> (F a ~> F b);
    Fhom_eqv: forall a b, Proper (eqv ==> eqv) (Fhom a b);
  }.
HB.builders Context 𝐂 𝐃 F of IsPreFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := IsDiagram.Build _ _ F Fhom.
  HB.instance Definition _ := Diagram_IsPreFunctor.Build _ _ F Fhom_eqv.
HB.end.

(** alternative factory, when the action on morphisms is already registered as extensional *)
HB.factory Record IsPreFunctor' (𝐂 𝐃: Quiver) (F: FUN 𝐂 𝐃) := {
    Fhom: forall a b, (a ~> b) -eqv-> (F a ~> F b);
  }.
HB.builders Context 𝐂 𝐃 F of IsPreFunctor' 𝐂 𝐃 F.
  HB.instance Definition _ := @IsPreFunctor.Build _ _ F Fhom (fun _ _ => extensional _).
HB.end.

(** ** functors: precategory morphisms, i.e., prefunctors + laws *)
#[primitive] HB.mixin Record HasFunctorLaws (𝐂 𝐃: PreCat) F of @PREFUNCTOR 𝐂 𝐃 F := {
    #[canonical=no] Fidmap: forall a: ob 𝐂, Fhom F a ≡ F a;
    #[canonical=no] Fcomp: forall (a b c: ob 𝐂) (f: a ~> b) (g: b ~> c), Fhom F (f \; g) ≡ Fhom F f \; Fhom F g;
  }.
#[short(type="Functor")]
HB.structure Definition FUNCTOR (𝐂 𝐃: PreCat) :=
  { F of HasFunctorLaws 𝐂 𝐃 F & }.
Arguments Fidmap {_ _ _ _}.
Arguments Fcomp {_ _ _ _ _ _}.

(** intermediate factory, for constructing functors from diagrams *)
HB.factory Record Diagram_IsFunctor (𝐂 𝐃: PreCat) F of @DIAGRAM 𝐂 𝐃 F := {
   Fhom_eqv: forall a b: ob 𝐂, Proper (eqv ==> eqv) (@Fhom _ _ F a b);
   Fidmap: forall a: ob 𝐂, Fhom F a ≡ idmap (F a);
   Fcomp: forall (a b c: ob 𝐂) (f: a ~> b) (g: b ~> c), Fhom F (g ∘ f) ≡ Fhom F g ∘ Fhom F f;
  }.
HB.builders Context 𝐂 𝐃 F of Diagram_IsFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := IsPreFunctor.Build _ _ F Fhom_eqv.
  HB.instance Definition _ := HasFunctorLaws.Build _ _ F Fidmap Fcomp.
HB.end.

(** direct factory, for constructing functors from scratch *)
HB.factory Record IsFunctor (𝐂 𝐃: PreCat) (F: FUN 𝐂 𝐃) := {
   Fhom: forall {A B: ob 𝐂}, (A ~> B) -> (F A ~> F B);
   Fhom_eqv: forall {A B: ob 𝐂}, Proper (eqv ==> eqv) (@Fhom A B);
   Fidmap: forall A: ob 𝐂, Fhom A ≡ idmap (F A);
   Fcomp: forall {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C), Fhom (g ∘ f) ≡ Fhom g ∘ Fhom f;
  }.
HB.builders Context 𝐂 𝐃 F of IsFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := IsDiagram.Build _ _ F Fhom.
  HB.instance Definition _ := Diagram_IsFunctor.Build _ _ F Fhom_eqv Fidmap Fcomp.
HB.end.

(** * faithful functors *)

(** faithful (pre)functor: + injectivity on morphisms *)
#[primitive] HB.mixin Record IsFaithful (𝐂 𝐃: Quiver) F of @PREFUNCTOR 𝐂 𝐃 F := {
    #[canonical=no] Fhom_inj: forall a b: ob 𝐂, injective (@Fhom _ _ F a b);
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

HB.factory Record IsFaithfulPreFunctor (𝐂 𝐃: Quiver) (F: FUN 𝐂 𝐃) := {
    Fhom: forall {A B}, (A ~> B) -> (F A ~> F B);
    Fhom_bij: forall {A B} (f g: A ~> B), Fhom f ≡ Fhom g <-> f ≡ g;
  }.
HB.builders Context 𝐂 𝐃 F of @IsFaithfulPreFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := @IsPreFunctor.Build _ _ F Fhom (fun _ _ f g => proj2 (Fhom_bij f g)).
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

Definition funcop {𝐂 𝐃} (F: FUN 𝐂 𝐃): FUN 𝐂^op 𝐃^op := F.
Definition funcop' {𝐂 𝐃} (F: FUN 𝐂^op 𝐃^op): FUN 𝐂 𝐃 := F.

HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: Diagram 𝐂 𝐃) :=
  IsDiagram.Build _ _ (funcop F) (fun _ _ => Fhom F).
HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: Diagram 𝐂^op 𝐃^op) :=
  IsDiagram.Build _ _ (funcop' F) (fun _ _ => Fhom F).

HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂 𝐃) :=
  Diagram_IsPreFunctor.Build _ _ (funcop F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂^op 𝐃^op) :=
  Diagram_IsPreFunctor.Build _ _ (funcop' F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).

HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂 𝐃) :=
  HasFunctorLaws.Build _ _ (funcop F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂^op 𝐃^op) :=
  HasFunctorLaws.Build _ _ (funcop' F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).

Definition funcop12 {𝐂 𝐃} (F: FUN 𝐂^op 𝐃): FUN 𝐂 𝐃^op := F.
Definition funcop21 {𝐂 𝐃} (F: FUN 𝐂 𝐃^op): FUN 𝐂^op 𝐃 := F.

HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: Diagram 𝐂^op 𝐃) :=
  IsDiagram.Build _ _ (funcop12 F) (fun _ _ => Fhom F).
HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: Diagram 𝐂 𝐃^op) :=
  IsDiagram.Build _ _ (funcop21 F) (fun _ _ => Fhom F).

HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂^op 𝐃) :=
  Diagram_IsPreFunctor.Build _ _ (funcop12 F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor 𝐂 𝐃^op) :=
  Diagram_IsPreFunctor.Build _ _ (funcop21 F) (fun _ _ _ _ => @Fhom_eqv _ _ F _ _ _ _).

HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂^op 𝐃) :=
  HasFunctorLaws.Build _ _ (funcop12 F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).
HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor 𝐂 𝐃^op) :=
  HasFunctorLaws.Build _ _ (funcop21 F) (@Fidmap _ _ F) (fun _ _ _ _ _ => @Fcomp _ _ F _ _ _ _ _).

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
  IsPreFunctor'.Build 𝐂 𝐂 idfun (fun A B => types_id).
HB.instance Definition _ (𝐂: PreCat) :=
  HasFunctorLaws.Build 𝐂 𝐂 idfun (fun=> eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(** composition of functors *)
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: Diagram 𝐂 𝐃} {G: Diagram 𝐃 𝐄} :=
  IsDiagram.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom F)).
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: PreFunctor 𝐂 𝐃} {G: PreFunctor 𝐃 𝐄} :=
  IsPreFunctor'.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom F)).
Program Definition _comp_functor 𝐂 𝐃 𝐄 {F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  HasFunctorLaws.Build 𝐂 𝐄 (catcomp F G) _ _.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fidmap. Qed.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fcomp. Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_comp_functor 𝐂 𝐃 𝐄 F G.

(** constant functor *)
Definition cst {𝐂 𝐃: BareQuiver} (D: ob 𝐃) := fun of 𝐂 => D.
HB.instance Definition _ {𝐂: BareQuiver} {𝐃: BarePreCat} (D: 𝐃) :=
  IsDiagram.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (D: 𝐃) :=
  IsPreFunctor'.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) :=
  HasFunctorLaws.Build 𝐂 𝐃 (cst D) (fun=> eqv_refl)
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
HB.instance Definition _ (𝐂 𝐃: BareQuiver) := IsDiagram.Build (𝐂∧𝐃) 𝐂 fst (fun _ _ => fst).
HB.instance Definition _ (𝐂 𝐃: Quiver) := Diagram_IsPreFunctor.Build (𝐂∧𝐃) 𝐂 fst (fun _ _ _ _ => fst).
Lemma _fst_functor (𝐂 𝐃: PreCat): HasFunctorLaws (𝐂∧𝐃) 𝐂 fst.
Proof. split; done. Qed.
HB.instance Definition _ 𝐂 𝐃 := @_fst_functor 𝐂 𝐃.

HB.instance Definition _ (𝐂 𝐃: BareQuiver) := IsDiagram.Build (𝐂∧𝐃) 𝐃 snd (fun _ _ => snd).
HB.instance Definition _ (𝐂 𝐃: Quiver) := Diagram_IsPreFunctor.Build (𝐂∧𝐃) 𝐃 snd (fun _ _ _ _ => snd).
Lemma _snd_functor (𝐂 𝐃: PreCat): HasFunctorLaws (𝐂∧𝐃) 𝐃 snd.
Proof. split; done. Qed.
HB.instance Definition _ 𝐂 𝐃 := @_snd_functor 𝐂 𝐃.

HB.instance Definition _ I (𝐂: I -> BareQuiver) i := IsDiagram.Build (forall i, 𝐂 i) (𝐂 i) (app i) (fun _ _ => app i).
HB.instance Definition _ I (𝐂: I -> Quiver) i := Diagram_IsPreFunctor.Build (forall i, 𝐂 i) (𝐂 i) (app i) (fun _ _ _ _ => app i).
Lemma _app_functor I (𝐂: I -> PreCat) i: HasFunctorLaws (forall i, 𝐂 i) (𝐂 i) (app i).
Proof. split; done. Qed.
HB.instance Definition _ I 𝐂 i := @_app_functor I 𝐂 i.


(** * Natural transformations *)

(** tranformations *)
Definition TX {𝐂: Type} {𝐃: BareQuiver} (F G: FUN 𝐂 𝐃) := forall X, F X ~> G X.
Identity Coercion TX_app: TX >-> Funclass.

Definition is_natural {𝐂: BareQuiver} {𝐃: PreCat} (F G: Diagram 𝐂 𝐃) (n: TX F G) :=
  forall (X Y: ob 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X.
Arguments is_natural {_ _ _ _} _/.

(** naturality *)
#[primitive] HB.mixin Record IsNatural {𝐂: BareQuiver} {𝐃: PreCat} (F G: Diagram 𝐂 𝐃) (n: TX F G) :=
  { #[canonical=no] natural: is_natural n }.
#[short(type="NTX")]
HB.structure Definition NATURAL 𝐂 𝐃 F G :=
  { n of @IsNatural 𝐂 𝐃 F G n }.
Arguments natural {_ _ _ _} _ [_ _] _.
Definition mk_ntx {𝐂: BareQuiver} {𝐃: PreCat} (F G: Diagram 𝐂 𝐃)
  (n: TX F G) (H: is_natural n)
  := HB.pack_for (NTX F G) n (IsNatural.Build _ _ F G n H).
Arguments mk_ntx {_ _} _ _ _ _.

(** duality *)
Definition ntxop {𝐂 𝐃 F G} (n: @TX 𝐂 𝐃 F G): TX (funcop G) (funcop F) := n. 
Definition ntxop' {𝐂 𝐃 F G} (n: TX F G): @TX 𝐂 𝐃 (funcop' G) (funcop' F) := n.

HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: Diagram 𝐂 𝐃) (n: NTX F G) :=
  IsNatural.Build _ _ _ _ (ntxop n) (fun _ _ _ => eqv_sym _ _ (natural n _)).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: Diagram _ _) (n: NTX F G) :=
  IsNatural.Build 𝐂 𝐃 _ _ (ntxop' n) (fun _ _ _ => eqv_sym _ _ (natural n _)).

Definition ntxop12 {𝐂 𝐃 F G} (n: @TX _ 𝐃 F G): @TX 𝐂 _ (funcop12 G) (funcop12 F) := n. 
Definition ntxop21 {𝐂 𝐃 F G} (n: @TX 𝐂 _ F G): @TX _ 𝐃 (funcop21 G) (funcop21 F) := n.

HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: Diagram _ 𝐃) (n: NTX F G) :=
  IsNatural.Build 𝐂 _ _ _ (ntxop12 n) (fun _ _ _ => eqv_sym _ _ (natural n _)).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: Diagram 𝐂 _) (n: NTX F G) :=
  IsNatural.Build _ 𝐃 _ _ (ntxop21 n) (fun _ _ _ => eqv_sym _ _ (natural n _)).


(** setoid structure on natural transformations *)
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: Diagram 𝐂 𝐃) :=
  Setoid.copy (NTX F G) (kernel (@NATURAL.sort 𝐂 𝐃 F G)).

(** ** categories of diagrams and natural transformations *)
HB.instance Definition _  𝐂 (𝐃: PreCat) :=
  IsQuiver.Build (Diagram 𝐂 𝐃) (@NTX 𝐂 𝐃).

Definition ntx_id_ 𝐂 {𝐃: PreCat} (F: Diagram 𝐂 𝐃): TX F F :=
  fun X => idmap (F X).
Arguments ntx_id_ {_ _} _ _ /. 
Lemma _ntx_id_natural 𝐂 (𝐃: Cat) (F: Diagram 𝐂 𝐃):
  IsNatural 𝐂 𝐃 F F (ntx_id_ F).
Proof. constructor=>X Y f/=. cat. Qed.
HB.instance Definition _ 𝐂 𝐃 F := @_ntx_id_natural 𝐂 𝐃 F.
Definition ntx_id {𝐂} {𝐃: Cat} (F: Diagram 𝐂 𝐃): F ~> F := (ntx_id_ F: NTX _ _).

Definition ntx_comp_ {𝐂} {𝐃: PreCat} (F G H: Diagram 𝐂 𝐃) (m: TX F G) (n: TX G H): TX F H :=
  fun X => n X ∘ m X.
Arguments ntx_comp_ {_ _ _ _ _} _ _ _/. 
Lemma _ntx_comp_natural 𝐂 (𝐃: Cat) (F G H: Diagram 𝐂 𝐃) (m: NTX F G) (n: NTX G H) :
  IsNatural 𝐂 𝐃 F H (@ntx_comp_ 𝐂 𝐃 F G H m n).
Proof.
  constructor=>A B f /=.
  by rewrite -compoA natural compoA natural compoA.
Qed.
HB.instance Definition _ 𝐂 𝐃 F G H m n := @_ntx_comp_natural 𝐂 𝐃 F G H m n.
Definition ntx_comp {𝐂} {𝐃: Cat} (F G H: Diagram 𝐂 𝐃) (n: F ~> G) (m: G ~> H): F ~> H :=
  (ntx_comp_ n m: NTX _ _). 

HB.instance Definition _ 𝐂 (𝐃: Cat) :=
  IsPreCat.Build (Diagram 𝐂 𝐃) ntx_id ntx_comp.

Lemma _diagram_cat 𝐂 (𝐃: Cat): IsCat (Diagram 𝐂 𝐃).
Proof.
  constructor; repeat intro. 
  - exact: comp1o. 
  - exact: compo1. 
  - exact: compoA. 
  - exact: comp_eqv.
Qed.
HB.instance Definition _ 𝐂 𝐃 := _diagram_cat 𝐂 𝐃.

(** ** full subcategories of prefunctors/functors and natural transformations *)

HB.instance Definition _ 𝐂 (𝐃: Cat) :=
  CAT.copy (PreFunctor 𝐂 𝐃) (kernel (@functor_PREFUNCTOR__to__functor_DIAGRAM 𝐂 𝐃)).

HB.instance Definition _ 𝐂 (𝐃: Cat) :=
  CAT.copy (Functor 𝐂 𝐃) (kernel (@functor_FUNCTOR__to__functor_PREFUNCTOR 𝐂 𝐃)).

(** casting isos between those subcategories *)

(* TODO: general kernel-based construction *)
Definition iso_prefunctor 𝐂 (𝐃: Cat) (F G: PreFunctor 𝐂 𝐃) (i: F ≃_(Diagram _ _) G): F ≃ G :=
  @iso_ (PreFunctor _ _) _ _ (i¹) (i⁻¹) (isoP i).

Definition iso_functor 𝐂 (𝐃: Cat) (F G: Functor 𝐂 𝐃) (i: F ≃_(Diagram _ _) G): F ≃ G :=
  @iso_ (Functor _ _) _ _ (i¹) (i⁻¹) (isoP i).

(* Check fun (𝐂: Cat) (F: Functor 𝐂 𝐂) (f: F ~> F) => let G: PreFunctor _ _ := F in f: G ~> G. *)

Definition ntx_comp'_ 𝐂 𝐃 {𝐄: PreCat} {F G: Diagram 𝐂 𝐃} {F' G': Diagram 𝐃 𝐄}
  (k: TX F G) (h: TX F' G'): TX (catcomp F F') (catcomp G G') :=
  (fun X => h _ ∘ Fhom _ (k _)).
Arguments ntx_comp'_ {_ _ _ _ _ _ _} _ _ _/. 
Program Definition _ntx_comp'_natural 𝐂 (𝐃: PreCat) (𝐄: Cat) (F G: Diagram 𝐂 𝐃) (F': Diagram 𝐃 𝐄) (G': Functor 𝐃 𝐄)
  (k: NTX F G) (h: NTX F' G') := IsNatural.Build 𝐂 𝐄 (catcomp F F') (catcomp G G') (ntx_comp'_ k h) _.
Next Obligation.
  cbn; intros.
  rewrite natural -compoA !natural.
  rewrite compoA -Fcomp natural.
  Fail cat.                     (* was working before *)
  rewrite Fcomp. cat.
Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G F' G' k h := @_ntx_comp'_natural 𝐂 𝐃 𝐄 F G F' G' k h.
Definition ntx_comp' {𝐂 𝐃 𝐄: Cat} {F G: Functor 𝐂 𝐃} {F' G': Functor 𝐃 𝐄}
  (*TMP-UNIV: functor_comp -> ∘ once we have Cat:Cat  *)
  (n: F ~> G) (m: F' ~> G'): (functor_comp F F') ~> (functor_comp G G') :=
  (ntx_comp'_ n m: NTX _ _). 
Notation "h ⊚ k" := (ntx_comp' k h): cat_scope. (* TODO: reverse this notation! *)




(** ** functor equivalence (i.e., natural isomorphisms) *)



(* there are several coercions from natural isomorphisms to pointwise morphisms,
   since we have categories of Diagrams/PreFunctors/Functors *)

Definition iso_ntx_pw1 {𝐂} {𝐃: Cat} (F G: Diagram 𝐂 𝐃) (n: F ≃ G) a: F a ~> G a := n¹ a.
HB.instance Definition _ 𝐂 𝐃 F G n a :=
   @IsIso.Build _ _ _ (@iso_ntx_pw1 𝐂 𝐃 F G n a) (inv n a) (invKl n a, invKr n a).

Definition iso_ntx_pw2 {𝐂} {𝐃: Cat} (F G: PreFunctor 𝐂 𝐃) (n: F ≃ G) a: F a ~> G a := n¹ a.
HB.instance Definition _ 𝐂 𝐃 F G n a :=
   @IsIso.Build _ _ _ (@iso_ntx_pw2 𝐂 𝐃 F G n a) (inv n a) (invKl n a, invKr n a).

Definition iso_ntx_pw3 {𝐂} {𝐃: Cat} (F G: Functor 𝐂 𝐃) (n: F ≃ G) a: F a ~> G a := n¹ a.
HB.instance Definition _ 𝐂 𝐃 F G n a :=
   @IsIso.Build _ _ _ (@iso_ntx_pw3 𝐂 𝐃 F G n a) (inv n a) (invKl n a, invKr n a).

(* unfortunately, we cannot declare the three coercions alltogether *)
(* TOTHINK: use elpi? (failed so far, because we return dependent function types) *)
Coercion iso_ntx_pw3: Iso >-> Funclass.

Check fun {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃) (i: F ≃ G) (X: ob 𝐂) => i X.
Check fun {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃) (i: F ≃ G) (X: ob 𝐂) => i X: _ ≃ _.
Check fun {𝐂 𝐃: Cat} (F G: Functor 𝐂 𝐃) (i: F ≃ G) (X: ob 𝐂) => unify (i⁻¹ X)  (i X)⁻¹.

Fail Check fun {𝐂 𝐃: Cat} (F G: Diagram 𝐂 𝐃) (i: F ≃ G) (X: ob 𝐂) => i X.
Check fun {𝐂 𝐃: Cat} (F G: Diagram 𝐂 𝐃) (i: F ≃ G) (X: ob 𝐂) => iso_ntx_pw1 i X.

Definition is_iso_tx 𝐂 (𝐃: PreCat) (F G: Diagram 𝐂 𝐃) (i: TX F G) (j: TX G F) :=
  forall a, is_iso (i a) (j a).

Lemma iso_txC 𝐂 (𝐃: PreCat) (F G: Diagram 𝐂 𝐃) (i: TX F G) (j: TX G F):
  is_iso_tx i j -> is_iso_tx j i.
Proof. move=>H a. exact: isoC. Qed.

Section s.
Context {𝐂} {𝐃: Cat} (F G: Diagram 𝐂 𝐃).

Lemma iso_tx_id: is_iso_tx (ntx_id F) (ntx_id F).
Proof. move=>a. exact/iso_id. Qed.

Definition iso_tx_id': sig (is_iso_tx (ntx_id F)) := exist _ _ iso_tx_id.

(** natural isomorphisms can be constructed from pointwise isomorphisms *)
Program Definition iso_ntx_ (i: forall X, F X ≃ G X) (n: F ~> G) (H: forall X, n X ≡ i X): F ≃ G :=
  iso_ n (mk_ntx G F (fun X => (i X)⁻¹) _) _.
Next Obligation.
  intros=>/=X Y f. rewrite -iso_src.
  rewrite -H -compoA -natural.
  by rewrite compoA H invKr cats. 
Qed.
Next Obligation. move=>i n H. split; cbn=>A/=; by rewrite H isoP. Qed.

(** via natural tranformations which are pointwise isomorphisms *)
Definition iso_ntx (i: forall X, F X ≃ G X) (N: forall X Y h, i Y ∘ Fhom F h ≡ Fhom G h ∘ i X): F ≃ G.
Proof. exact: (@iso_ntx_ i (mk_ntx _ _ i N)). Defined.
Definition iso_ntx' (i: F ~> G) (j: TX G F) (ij: is_iso_tx i j): F ≃ G.
Proof.
  set i' := fun X => iso_ (i X) (j X) (ij X).
  exact: (@iso_ntx_ i' i (fun _ => eqv_refl)).
Defined.

(** when the functors actually are pointwise equal *)
Program Definition same_diagram
  (FG1: forall X, F X = G X)
  (FG2: forall (A B: ob 𝐂) (f: A ~> B),
      Fhom G f ≡ cast2' (T:=hom) (Fhom F f) (FG1 A) (FG1 B)): F ≃ G :=
  @iso_ntx _ _. 
Next Obligation.
  intros FG1 _ X. rewrite FG1. exact: iso_refl.
Defined.
Next Obligation.
  intros FG1 FG2 A B f. rewrite /= FG2 /cast2' /=/same_diagram_obligation_1.
  destruct (FG1 A); destruct (FG1 B).
  by simpl; cat. 
Qed.

End s.

Lemma iso_ntx_alt 𝐂 (𝐃: Cat) (F G: 𝐂 ≈> 𝐃) (i: F ≃ G) A B (f: A ~> B):
  Fhom G f ≡ i B ∘ Fhom F f ∘ (i A)⁻¹.
Proof. rewrite natural -compoA invKl. cat. Qed.

Lemma iso_ntx_eqv 𝐂 (𝐃: Cat) (F G: 𝐂 ≈> 𝐃) (i: F ≃ G) A B (f g: A ~> B):
  Fhom F f ≡ Fhom F g -> Fhom G f ≡ Fhom G g.
Proof. rewrite 2!(iso_ntx_alt i). by move=>->. Qed.

(* Check fun {𝐂 𝐃: Cat} (F G: 𝐂 ≈> 𝐃) (i: F ≈ G) (X: 𝐂) => unify (i⁻¹ X)  (i X)⁻¹. *)

Section strict.
Context {𝐂 𝐃 𝐄: Cat}.

Lemma ntx_comp'_id {F: 𝐂 ≈> 𝐃} {G: 𝐃 ≈> 𝐄}:
  idmap G ⊚ idmap F ≡ idmap.
Proof. intro X; cbn. by rewrite !cats. Qed.

Lemma ntx_comp'_comp {F G H: 𝐂 ≈> 𝐃} {F' G' H': 𝐃 ≈> 𝐄}
  (i: F ~> G) (j: G ~> H)
  (i': F' ~> G') (j': G' ~> H'):
  (j'∘i') ⊚ (j∘i) ≡ (j'⊚j) ∘ (i'⊚i).
Proof.
  intro X; cbn.
  rewrite -!compoA. apply: comp_eqv=>//.
  normalise. by rewrite natural.
Qed.

(* TOFIX: declaring this one as an instance results in super long
   steps in adjunction.v (_Frecomp_functor) *)
Lemma ntx_comp'_eqv {F G: 𝐂 ≈> 𝐃} {F' G': 𝐃 ≈> 𝐄}:
  Proper (eqv ==> eqv ==> eqv) (@ntx_comp' _ _ _ F G F' G').
Proof.
  intros i i' ii j j' jj X=>/=.
  by rewrite /= (ii _) (jj _).
Qed.

Import CMorphisms.
Program Definition functor_comp_iso:
  Proper (Iso ==> Iso ==> Iso) (@functor_comp 𝐂 𝐃 𝐄) :=
  fun F G i F' G' j => iso_ (j⊚ i) (j⁻¹⊚i⁻¹) _.
Next Obligation.
  split.
  - rewrite -ntx_comp'_comp; etransitivity.
    exact: (ntx_comp'_eqv (invKl i) (invKl j)).
    by rewrite ntx_comp'_id.
  - rewrite -ntx_comp'_comp; etransitivity.
    exact: (ntx_comp'_eqv (invKr i) (invKr j)).
    by rewrite ntx_comp'_id.
Qed.
End strict.

