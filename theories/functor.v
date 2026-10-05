(** * Functors, natural transformations, adjunctions *)

Require Export morphisms.
Require Import cast arewrite.

Local Open Scope cat_scope.

(** * Functors *)

(** prefunctor: a functor without laws *)
#[primitive] HB.mixin Record IsPreFunctor' (𝐂 𝐃: Quiver) (F: ob 𝐂 -> ob 𝐃) := {
   #[canonical=no] Fhom: forall A B: ob 𝐂, (A ~> B) -> (F A ~> F B);
   #[canonical=no] _Fhom_eqv: forall A B: ob 𝐂, Proper (eqv ==> eqv) (Fhom A B);
  }.
#[short(type="PreFunctor")]
HB.structure Definition prefunctor 𝐂 𝐃 :=
  { F of IsPreFunctor' 𝐂 𝐃 F }.
Arguments Fhom {_ _} _ {_ _}. 
Instance Fhom_eqv {𝐂 𝐃: Quiver} {F: PreFunctor 𝐂 𝐃} {A B: ob 𝐂}: Proper (eqv ==> eqv) (Fhom F) := _Fhom_eqv A B. 
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) A B :=
  isExtensional.Build _ _ (@Fhom _ _ F A B) _. 

(** alternative factory, when the action on morphisms is already registered as extensional *)
HB.factory Record IsPreFunctor (𝐂 𝐃: Quiver) (F: ob 𝐂 -> ob 𝐃) := {
    Fhom: forall {A B}, (A ~> B) -eqv-> (F A ~> F B);
  }.
HB.builders Context 𝐂 𝐃 F of @IsPreFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := @IsPreFunctor'.Build _ _ F Fhom (fun _ _ => extensional _).
HB.end.

(** functor: prefunctor + laws *)
#[primitive] HB.mixin Record IsFunctor (𝐂 𝐃: PreCat) F of @prefunctor 𝐂 𝐃 F := {
    #[canonical=no] _Fidmap: forall A: ob 𝐂, Fhom F A ≡ F A;
    #[canonical=no] _Fcomp: forall (A B C: ob 𝐂) (f: A ~> B) (g: B ~> C), Fhom F (f \; g) ≡ Fhom F f \; Fhom F g;
  }.
#[short(type="Functor")]
HB.structure Definition functor (𝐂 𝐃: PreCat) :=
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
  HB.instance Definition _ := @IsPreFunctor'.Build _ _ F Fhom Fhom_eqv.
  HB.instance Definition _ := IsFunctor.Build _ _ F Fidmap Fcomp.
HB.end.


(** faithful (pre)functor + injectivity on morphisms *)
#[primitive] HB.mixin Record IsFaithful (𝐂 𝐃: Quiver) F of @prefunctor 𝐂 𝐃 F := {
    #[canonical=no] Fhom_inj: forall {A B} (f g: A ~> B), Fhom F f ≡ Fhom F g -> f ≡ g;
  }.
#[short(type="FaithfulPreFunctor")]
HB.structure Definition faithfulprefunctor (𝐂 𝐃: Quiver) :=
  { F of IsFaithful 𝐂 𝐃 F & IsPreFunctor' 𝐂 𝐃 F }.
#[short(type="FaithfulFunctor")]
HB.structure Definition faithfulfunctor (𝐂 𝐃: PreCat) :=
  { F of @faithfulprefunctor 𝐂 𝐃 F & IsFunctor 𝐂 𝐃 F }.
Arguments Fhom_inj {_ _} _ {_ _}.

Lemma Fhom_bij 𝐂 𝐃 (F: FaithfulPreFunctor 𝐂 𝐃) {A B: ob 𝐂} (f g: A ~> B):
  Fhom F f ≡ Fhom F g <-> f ≡ g.
Proof. split. exact:Fhom_inj. exact/Fhom_eqv. Qed.

HB.factory Record IsFaithfulPreFunctor (𝐂 𝐃: Quiver) (F: ob 𝐂 -> ob 𝐃) := {
    Fhom: forall {A B}, (A ~> B) -> (F A ~> F B);
    Fhom_bij: forall {A B} (f g: A ~> B), Fhom f ≡ Fhom g <-> f ≡ g;
  }.
HB.builders Context 𝐂 𝐃 F of @IsFaithfulPreFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := IsPreFunctor'.Build _ _ F (fun _ _ f g => proj2 (Fhom_bij f g)).
  HB.instance Definition _ := IsFaithful.Build _ _ F (fun _ _ f g => proj1 (Fhom_bij f g)).
HB.end.

(** rewriting tuple *)
Definition cats := (@Fidmap, cats, @Fcomp)%core.

(** getting category laws from faithful functors *)
HB.factory Record FaithfulSubCat (𝐃: Cat)  𝐂 of precat 𝐂 := { F: FaithfulFunctor 𝐂 𝐃 }.
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
  

Definition funcop {A B} (F: ob A -> ob B): ob (A^op) -> ob (B^op) := F. 
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) :=
  @IsPreFunctor'.Build 𝐂^op 𝐃^op (funcop F) (fun _ _ f => Fhom F f)
                                (fun A B f g fg => @Fhom_eqv _ _ F B A f g fg).
HB.instance Definition _ 𝐂 𝐃 (F: Functor 𝐂 𝐃) :=
  @IsFunctor.Build 𝐂^op 𝐃^op (funcop F) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _). 
HB.instance Definition _ 𝐂 𝐃 (F: FaithfulPreFunctor 𝐂 𝐃) :=
  @IsFaithful.Build 𝐂^op 𝐃^op (funcop F) (fun A B => @Fhom_inj _ _ F B A). 
HB.instance Definition _ 𝐂 𝐃 (F: FaithfulFunctor 𝐂 𝐃) := 
  @IsFaithful.Build 𝐂^op 𝐃^op (funcop F) (fun A B => @Fhom_inj _ _ F B A). 




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
HB.instance Definition _ {𝐂 𝐃 𝐄: Quiver} {F: PreFunctor 𝐂 𝐃} {G: PreFunctor 𝐃 𝐄} :=
  IsPreFunctor.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom F)).
Program Definition _comp_functor {𝐂 𝐃 𝐄: PreCat} {F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  IsFunctor.Build 𝐂 𝐄 (catcomp F G) _ _.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fidmap. Qed.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fcomp. Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_comp_functor 𝐂 𝐃 𝐄 F G.

(** constant functor *)
Definition cst {𝐂 𝐃: Quiver} (D: ob 𝐃) := fun of 𝐂 => D.
HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (D: 𝐃) :=
  IsPreFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) :=
  IsFunctor.Build 𝐂 𝐃 (cst D) (fun=> eqv_refl)
    (fun _ _ _ _ _ => eqv_sym _ _ (compo1 idmap)).

Section s.
  Context {𝐂: PreCat} {𝐃: Cat} (F: Functor 𝐂 𝐃) (A B: ob 𝐂) (i: A ≃ B).
  Program Definition _functor_iso := @IsIso.Build _ _ _ (Fhom F i) (Fhom F i⁻¹) _ _.
  Next Obligation. intros. by rewrite -Fcomp invKl Fidmap. Qed.
  Next Obligation. intros. by rewrite -Fcomp invKr Fidmap. Qed.
  HB.instance Definition _ := _functor_iso.
End s.

(* waiting for universe polymorphism, we cannot declare the following instance *)
(* Unset Universe Checking. *)
(*TMP-UNIV
HB.instance Definition _ := IsBareQuiver.Build Cat Functor. 
*)
(* meanwhile, we use the following notation for functors; later we will replace it with "~>" *)
Notation "F ≈> G" := (Functor F G): cat_scope.
Definition functor_id {𝐂: Cat}: 𝐂 ≈> 𝐂 := idfun: Functor 𝐂 𝐂.
Definition functor_comp {𝐂 𝐃 𝐄: Cat} (F: 𝐂 ≈> 𝐃) (G: 𝐃 ≈> 𝐄): 𝐂 ≈> 𝐄 := catcomp F G: Functor _ _.
Definition functor_cst {𝐂 𝐃: Cat} (D: 𝐃): 𝐂 ≈> 𝐃 := cst D: Functor _ _.
(*TMP-UNIV
HB.instance Definition _ := IsPreCat.Build Cat (@functor_id) (@functor_comp). 
*)



(** * Natural transformations *)

(** naturality *)
#[primitive] HB.mixin Record IsNatural {𝐂: Quiver} {𝐃: PreCat} (F G: PreFunctor 𝐂 𝐃) (n : forall X, F X ~> G X) :=
  { #[canonical=no] natural: forall (X Y: ob 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X }.
#[short(type="NTX")]
HB.structure Definition Natural {𝐂: Quiver} {𝐃: PreCat} (F G: PreFunctor 𝐂 𝐃) :=
  { n of @IsNatural 𝐂 𝐃 F G n }.
Arguments natural {_ _ _ _} _ [_ _] _.
Definition mk_ntx {𝐂: Quiver} {𝐃: PreCat} (F G: PreFunctor 𝐂 𝐃)
  (n : forall X, F X ~> G X) (H: forall (X Y: ob 𝐂) (f: X ~> Y), n Y ∘ Fhom F f ≡ Fhom G f ∘ n X)
  := HB.pack_for (NTX F G) n (IsNatural.Build _ _ F G n H).
Arguments mk_ntx {_ _} _ _ _ _.

Definition ntxop {𝐂 𝐃: Quiver} (F G: ob 𝐂 -> ob 𝐃) (n: forall X, F X ~> G X): forall X, funcop G X ~> funcop F X
  := fun X => morphop (n X).

HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (F G: PreFunctor 𝐂 𝐃) (n: NTX F G) :=
  @IsNatural.Build 𝐂^op 𝐃^op (funcop G) (funcop F) (ntxop n) (fun _ _ f => eqv_sym _ _ (natural n f)).

(** setoid structure on natural transformations *)
HB.instance Definition _ (𝐂: Quiver) {𝐃: PreCat} (F G: PreFunctor 𝐂 𝐃) :=
  Setoid.copy (NTX F G) (kernel (@Natural.sort 𝐂 𝐃 F G)).

(** ** categories of (pre)functors and natural transformations *)
HB.instance Definition _  𝐂 (𝐃: PreCat) :=
  IsQuiver.Build (PreFunctor 𝐂 𝐃) (@NTX 𝐂 𝐃).
HB.instance Definition _  𝐂 𝐃 :=
  IsQuiver.Build (Functor 𝐂 𝐃) (@NTX 𝐂 𝐃).

Definition ntx_id_ 𝐂 {𝐃: PreCat} (F: PreFunctor 𝐂 𝐃) :=
  fun X => idmap (F X).
Arguments ntx_id_ {_ _} _ _ /. 
Lemma _ntx_id_natural 𝐂 (𝐃: Cat) (F: PreFunctor 𝐂 𝐃):
  IsNatural 𝐂 𝐃 F F (ntx_id_ F).
Proof. constructor=>X Y f/=. cat. Qed.
HB.instance Definition _ 𝐂 𝐃 F := @_ntx_id_natural 𝐂 𝐃 F.
Definition pre_ntx_id {𝐂} {𝐃: Cat} (F: PreFunctor 𝐂 𝐃): F ~> F := (ntx_id_ F: NTX _ _). 
Definition ntx_id {𝐂} {𝐃: Cat} (F: Functor 𝐂 𝐃): F ~> F := (ntx_id_ F: NTX _ _). 

Definition ntx_comp_ {𝐂} {𝐃: PreCat} (F G H: PreFunctor 𝐂 𝐃) (m: forall X, F X ~> G X) (n: forall X, G X ~> H X) :=
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

Definition ntx_comp'_ 𝐂 𝐃 {𝐄: PreCat} {F G: PreFunctor 𝐂 𝐃} {F' G': PreFunctor 𝐃 𝐄}
  (k: forall X, F X ~> G X) (h: forall X, F' X ~> G' X): forall X, (catcomp F F') X ~> (catcomp G G') X :=
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



#[primitive] 
HB.mixin Record IsPreAdjoint {𝐂 𝐃: Type} (F: ob 𝐂 -> ob 𝐃) :=
  { #[canonical=no] adj: ob 𝐃 -> ob 𝐂 }.
#[short(type="PreAdjoint")]
HB.structure Definition preAdjoint 𝐂 𝐃 := {F of IsPreAdjoint 𝐂 𝐃 F & }.
Arguments adj {_ _}.

HB.instance Definition _ {𝐂 𝐃: Type} (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐂^op 𝐃^op (funcop F) (adj F).
HB.instance Definition _ {𝐂 𝐃: Type} (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐃 𝐂 (adj F) F.

HB.instance Definition _ {𝐂: Type} := IsPreAdjoint.Build 𝐂 𝐂 idfun idfun.
HB.instance Definition _ {𝐂 𝐃 𝐄: Type} (F: PreAdjoint 𝐂 𝐃) (G: PreAdjoint 𝐃 𝐄) :=
  IsPreAdjoint.Build 𝐂 𝐄 (catcomp F G) (catcomp (adj G) (adj F)).

#[primitive] 
HB.mixin Record IsPreAdjointF {𝐂 𝐃: PreCat} F of @preAdjoint 𝐂 𝐃 F :=
  { #[canonical=no] _adj_functor: @functor.axioms_ _ _ (adj F) }.
#[short(type="PreAdjointF")]
HB.structure Definition preAdjointF 𝐂 𝐃 := {F of @functor 𝐂 𝐃 F & IsPreAdjointF _ _ F & IsPreAdjoint _ _ F}.
HB.instance Definition _ 𝐂 𝐃 F := @_adj_functor 𝐂 𝐃 F. 

HB.instance Definition _ {𝐂 𝐃: PreCat} (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointF.Build 𝐂^op 𝐃^op (funcop F) (functor.class (funcop (adj F))).
HB.instance Definition _ {𝐂 𝐃: PreCat} (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointF.Build 𝐃 𝐂 (adj F) (functor.class F).

HB.instance Definition _ {𝐂: Cat} := IsPreAdjointF.Build 𝐂 𝐂 idfun (functor.class functor_id).
HB.instance Definition _ {𝐂 𝐃 𝐄: Cat} (F: PreAdjointF 𝐂 𝐃) (G: PreAdjointF 𝐃 𝐄) :=
  IsPreAdjointF.Build 𝐂 𝐄 (catcomp F G) (functor.class (functor_comp (adj G) (adj F))).


#[primitive] HB.mixin Record IsLeftAdjoint {𝐂 𝐃: Cat} F of @preAdjointF 𝐂 𝐃 F :=
  { #[canonical=no] unit: functor_id ~> functor_comp F (adj F);
    #[canonical=no] counit: functor_comp (adj F) F ~> functor_id;
    #[canonical=no] unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _;
    #[canonical=no] unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _;
  }.
#[short(type="LeftAdjoint")]
HB.structure Definition leftAdjoint 𝐂 𝐃 := {F of IsLeftAdjoint 𝐂 𝐃 F & }.
Infix "⊣" := LeftAdjoint (at level 79): cat_scope.
Arguments unit {_ _ _}, {_ _} _.
Arguments counit {_ _ _}, {_ _} _.

Program Definition _leftAdjoint_id 𝐂 := @IsLeftAdjoint.Build 𝐂 𝐂 idfun (ntx_id _) (ntx_id _) _ _.
Next Obligation. cbn=>*. by rewrite !cats. Qed.
Next Obligation. cbn=>*. by rewrite !cats. Qed.
HB.instance Definition _ 𝐂 := @_leftAdjoint_id 𝐂.

Program Definition _leftAdjoint_comp 𝐂 𝐃 𝐄 (F: 𝐂 ⊣ 𝐃) (G: 𝐃 ⊣ 𝐄) :=
  @IsLeftAdjoint.Build 𝐂 𝐄 (catcomp F G)
    (unit F \; idmap ⊚ unit G ⊚ idmap) (idmap ⊚ counit F ⊚ idmap \; counit G) _ _.
Admit Obligations.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_leftAdjoint_comp 𝐂 𝐃 𝐄 F G. 


#[primitive] HB.mixin Record IsRightAdjoint {𝐂 𝐃: Cat} F of @preAdjointF 𝐂 𝐃 F :=
  { #[canonical=no] unit': functor_id ~> functor_comp (adj F) F;
    #[canonical=no] counit': functor_comp F (adj F) ~> functor_id;
    #[canonical=no] unit_counit_l': idmap ⊚ unit' \; counit' ⊚ idmap ≡ ntx_id _;
    #[canonical=no] unit_counit_r': unit' ⊚ idmap \; idmap ⊚ counit' ≡ ntx_id _;
  }.
#[short(type="RightAdjoint")]
HB.structure Definition rightAdjoint 𝐂 𝐃 := {F of IsRightAdjoint 𝐂 𝐃 F & }.
Infix "⊢" := RightAdjoint (at level 79): cat_scope.
Arguments unit' {_ _ _}, {_ _} _.
Arguments counit' {_ _ _}, {_ _} _.

Program Definition _rightAdjoint_id 𝐂 := @IsRightAdjoint.Build 𝐂 𝐂 idfun (ntx_id _) (ntx_id _) _ _.
Next Obligation. cbn=>*. by rewrite !cats. Qed.
Next Obligation. cbn=>*. by rewrite !cats. Qed.
HB.instance Definition _ 𝐂 := @_rightAdjoint_id 𝐂.

Program Definition _rightAdjoint_comp 𝐂 𝐃 𝐄 (F: 𝐂 ⊢ 𝐃) (G: 𝐃 ⊢ 𝐄) :=
  @IsRightAdjoint.Build 𝐂 𝐄 (catcomp F G)
    (unit' G \; idmap ⊚ unit' F ⊚ idmap) (idmap ⊚ counit' G ⊚ idmap \; counit' F) _ _.
Admit Obligations.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_rightAdjoint_comp 𝐂 𝐃 𝐄 F G. 

HB.instance Definition _ {𝐂 𝐃: Cat} (F: 𝐂 ⊣ 𝐃) :=
  IsRightAdjoint.Build 𝐃 𝐂 (adj F) unit_counit_l unit_counit_r.
HB.instance Definition _ {𝐂 𝐃: Cat} (F: 𝐂 ⊢ 𝐃) :=
  IsLeftAdjoint.Build 𝐃 𝐂 (adj F) unit_counit_l' unit_counit_r'.

Program Definition _right_adjoint_funcop {𝐂 𝐃: Cat} (F: 𝐂 ⊣ 𝐃) :=
  @IsRightAdjoint.Build 𝐂^op 𝐃^op (funcop F) (ntxop (counit F): NTX _ _) (ntxop (unit F): NTX _ _) _ _.
Next Obligation.
  intros. cbn=>X. move: (@unit_counit_r _ _ F X). cbn.
  rewrite /ntxop/morphop/types_id/=!cats. exact.
Qed.
Next Obligation.
  intros. cbn=>X. move: (@unit_counit_l _ _ F X). cbn.
  rewrite /ntxop/morphop/types_id/=!cats. exact.
Qed.
HB.instance Definition _ 𝐂 𝐃 F := @_right_adjoint_funcop 𝐂 𝐃 F . 

Program Definition _left_adjoint_funcop {𝐂 𝐃: Cat} (F: 𝐂 ⊢ 𝐃) :=
  @IsLeftAdjoint.Build 𝐂^op 𝐃^op (funcop F) (ntxop (counit' F): NTX _ _) (ntxop (unit' F): NTX _ _) _ _.
Next Obligation.
  intros. cbn=>X. move: (@unit_counit_r' _ _ F X). cbn.
  rewrite /ntxop/morphop/types_id/=!cats. exact.
Qed.
Next Obligation.
  intros. cbn=>X. move: (@unit_counit_l' _ _ F X). cbn.
  rewrite /ntxop/morphop/types_id/=!cats. exact.
Qed.
HB.instance Definition _ 𝐂 𝐃 F := @_left_adjoint_funcop 𝐂 𝐃 F . 

#[short(type="AdjointEquivalence")]
HB.structure Definition adjointEquivalence {𝐂 𝐃: Cat} :=
  {F of @leftAdjoint 𝐂 𝐃 F & @rightAdjoint 𝐂 𝐃 F }.

(* TOFIX: declarations below are no-ops *)
HB.saturate adj. 
HB.saturate funcop. 
HB.saturate idfun. 
HB.saturate catcomp. 
(* we emulate them using the following asymmetric declarations *)
HB.instance Definition _ (C D: Cat) (F: AdjointEquivalence C D) := leftAdjoint.on (adj F).
HB.instance Definition _ (C D: Cat) (F: AdjointEquivalence C D) := leftAdjoint.on (funcop F).
HB.instance Definition _ (C: Cat) := leftAdjoint.on (@idfun C).
HB.instance Definition _ (C D E: Cat) (F: AdjointEquivalence C D) (G: AdjointEquivalence D E) := leftAdjoint.on (catcomp F G).
Check fun (C D: Cat) (F: AdjointEquivalence C D) => adj F: AdjointEquivalence D C. 
Check fun (C D: Cat) (F: AdjointEquivalence C D) => funcop F: AdjointEquivalence (C^op) (D^op). 
Check fun (C: Cat) => idfun: AdjointEquivalence C C. 


HB.factory Record IsAdjointEquivalence {𝐂 𝐃: Cat} F of @preAdjointF 𝐂 𝐃 F :=
  { adjKl: functor_comp (adj F) F ≃ functor_id;
    adjKr: functor_comp F (adj F) ≃ functor_id;
    unit_counit_l: idmap ⊚ adjKr⁻¹ \; adjKl ⊚ idmap ≡ ntx_id _;
    unit_counit_r: adjKr⁻¹ ⊚ idmap \; idmap ⊚ adjKl ≡ ntx_id _;
  }.
HB.builders Context 𝐂 𝐃 F of @IsAdjointEquivalence 𝐂 𝐃 F.
  HB.instance Definition _ := @IsLeftAdjoint.Build 𝐂 𝐃 F adjKr⁻¹ adjKl unit_counit_l unit_counit_r.  
  Lemma unit_counit_l': idmap ⊚ adjKl⁻¹ \; adjKr ⊚ idmap ≡ ntx_id _.
  Admitted.
  Lemma unit_counit_r': adjKl⁻¹ ⊚ idmap \; idmap ⊚ adjKr ≡ ntx_id _.
  Admitted.
  HB.instance Definition _ := @IsRightAdjoint.Build 𝐂 𝐃 F adjKl⁻¹ adjKr unit_counit_l' unit_counit_r'.  
HB.end.

Section theory.
Context {𝐂 𝐃: Cat} (F: 𝐂 ⊣ 𝐃).

Lemma unit_counit_l_at A: Fhom F (unit F A) \; counit F (F A) ≡ idmap.
Proof. move: (@unit_counit_l _ _ F A)=>/=. by rewrite !cats. Qed.
Lemma unit_counit_r_at B: unit F (adj F B) \; Fhom (adj F) (counit F B) ≡ idmap.
Proof. move: (@unit_counit_r _ _ F B)=>/=. by rewrite !cats. Qed.

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
  rewrite /dn/up/=.
  rewrite Fcomp.                (* FIXRW *)
  arewrite (natural counit). 
  arewrite unit_counit_l_at.
  cat. 
Qed.

Lemma up_inj {A B} (f f': F A ~> B): up f ≡ up f' -> f ≡ f'.
Proof. move=>H. rewrite -(dn_up f) -(dn_up f'). exact/dn_eqv. Qed.

Lemma up_dn {A B} (f: A ~> adj F B): up (dn f) ≡ f.
Proof.
  rewrite /dn/up/=.
  rewrite Fcomp.                (* FIXRW *)
  arewrite -(natural unit). 
  arewrite unit_counit_r_at.
  cat. 
Qed.

Lemma dn_inj {A B} (f f': A ~> adj F B): dn f ≡ dn f' -> f ≡ f'.
Proof. move=>H. rewrite -(up_dn f) -(up_dn f'). exact/up_eqv. Qed.

End theory.


(** ** functor equivalence (i.e., natural isomorphisms) *)

Section s.
Context {𝐂} {𝐃: Cat} (F G: Functor 𝐂 𝐃).
Definition functor_equiv := F ≃ G.

(** alternative constructors for natural isomorphisms  *)
Program Definition iso_ntx'
  (i: forall X, F X ≃ G X) (n: F ~> G)
  (H: forall X, n X ≡ i X): functor_equiv :=
  mk_iso n (mk_ntx G F (fun X => (i X)⁻¹) _) _ _.
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
  mk_iso (i¹ X) (i⁻¹ X) (invKl i X) (invKr i X). 

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
Proof. intros i i' ii j j' jj X. by rewrite /= (ii _) (jj _). Qed.

(* Lemma functor_comp_eqv: *)
(*   Proper (eqv ==> eqv ==> eqv) (@functor_comp 𝐂 𝐃 𝐄). *)
(* Proof. *)
(*   intros F G [i] F' G' [j]. split.   *)
(*   apply: (mk_iso' (j⊚ i) (j⁻¹⊚i⁻¹) _ _). *)
(*   rewrite endo_exchange. *)
(*   etransitivity. exact: (ntx_comp'_eqv (invKl i) (invKl j)). by rewrite -ntx_id_comp.  *)
(*   rewrite endo_exchange. *)
(*   etransitivity. exact: (ntx_comp'_eqv (invKr i) (invKr j)). by rewrite -ntx_id_comp.  *)
(* Qed. *)
End strict.

(*TMP-UNIV 
Program Definition _cat_cat := IsCat.Build Cat _ _ _ _.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. intros. exact: functor_comp_eqv. Qed.
HB.instance Definition _ := _cat_cat.
*)

Definition biop {𝐂: Quiver} (x: ob 𝐂): 𝐂^op^op := obop (obop x).
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreFunctor'.Build 𝐂 (𝐂^op^op) biop (fun _ _ _ _ H => H).
HB.instance Definition _ (𝐂: PreCat) :=
  IsFunctor.Build 𝐂 (𝐂^op^op) biop (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

Definition biop' {𝐂: Quiver} (x: 𝐂^op^op): ob 𝐂 := x.
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreFunctor'.Build (𝐂^op^op) 𝐂 biop' (fun _ _ _ _ H => H).
HB.instance Definition _ (𝐂: PreCat) :=
  IsFunctor.Build (𝐂^op^op) 𝐂 biop' (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ (𝐂: PreCat) := IsPreAdjoint.Build 𝐂 𝐂^op^op biop biop'. 
HB.instance Definition _ (𝐂: PreCat) := IsPreAdjointF.Build 𝐂 𝐂^op^op biop (functor.class biop'). 
Program Definition _biop_ladj (𝐂: Cat) := @IsLeftAdjoint.Build 𝐂 𝐂^op^op biop (ntx_id _) (ntx_id _) _ _.
Next Obligation. cbn=>? a. cat. Qed.
Next Obligation. cbn=>? a. cat. Qed.
HB.instance Definition _ 𝐂 := _biop_ladj 𝐂.
Program Definition _biop_radj (𝐂: Cat) := @IsRightAdjoint.Build 𝐂 𝐂^op^op biop (ntx_id _) (ntx_id _) _ _.
Next Obligation. cbn=>? a. cat. Qed.
Next Obligation. cbn=>? a. cat. Qed.
HB.instance Definition _ 𝐂 := _biop_radj 𝐂.

