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


(** * contravariant functors *)

(** contravariant bare prefunctors *)
#[primitive] HB.mixin Record IsBarePreContravariantFunctor (𝐂 𝐃: BareQuiver) (F: ob 𝐂 -> ob 𝐃) := {
   #[canonical=no] Fhom': forall A B: ob 𝐂, (A ~> B) -> (F B ~> F A);
  }.
#[short(type="BarePreContravariantFunctor")]
HB.structure Definition BAREPRECONTRAVARIANTFUNCTOR 𝐂 𝐃 :=
  { F of IsBarePreContravariantFunctor 𝐂 𝐃 F }.
Arguments Fhom' {_ _} _ {_ _}. 

(** contravariant prefunctor: a contravariant functor without laws *)
#[primitive] HB.mixin Record IsPreContravariantFunctor' (𝐂 𝐃: Quiver) F of @BAREPRECONTRAVARIANTFUNCTOR 𝐂 𝐃 F := {
   #[canonical=no] _Fhom'_eqv: forall A B: ob 𝐂, Proper (eqv ==> eqv) (@Fhom' _ _ F A B);
  }.
#[short(type="PreContravariantFunctor")]
HB.structure Definition PRECONTRAVARIANTFUNCTOR 𝐂 𝐃 :=
  { F of IsPreContravariantFunctor' 𝐂 𝐃 F & }.
Instance Fhom'_eqv {𝐂 𝐃} {F: PreContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂}: Proper (eqv ==> eqv) (Fhom' F) := _Fhom'_eqv A B. 
HB.instance Definition _ 𝐂 𝐃 (F: PreContravariantFunctor 𝐂 𝐃) A B :=
  isExtensional.Build _ _ (@Fhom' _ _ F A B) _. 

(** alternative factory, when the action on morphisms is already registered as extensional *)
HB.factory Record IsPreContravariantFunctor (𝐂 𝐃: Quiver) (F: ob 𝐂 -> ob 𝐃) := {
    Fhom': forall {A B}, (A ~> B) -eqv-> (F B ~> F A);
  }.
HB.builders Context 𝐂 𝐃 F of @IsPreContravariantFunctor 𝐂 𝐃 F.
  HB.instance Definition _ := IsBarePreContravariantFunctor.Build _ _ F Fhom'.
  HB.instance Definition _ := IsPreContravariantFunctor'.Build _ _ F (fun _ _ => extensional _).
HB.end.

(** contravariant: add laws *)
#[primitive] HB.mixin Record IsContravariantFunctor (𝐂 𝐃: PreCat) F of @PRECONTRAVARIANTFUNCTOR 𝐂 𝐃 F := {
    #[canonical=no] _Fidmap': forall A: ob 𝐂, Fhom' F A ≡ F A;
    #[canonical=no] _Fcomp': forall (A B C: ob 𝐂) (f: A ~> B) (g: B ~> C), Fhom' F (f \; g) ≡ Fhom' F g \; Fhom' F f;
  }.
#[short(type="ContravariantFunctor")]
HB.structure Definition CONTRAVARIANTFUNCTOR 𝐂 𝐃 :=
  { F of IsContravariantFunctor 𝐂 𝐃 F & }.
Definition Fidmap' {𝐂 𝐃} {F: ContravariantFunctor 𝐂 𝐃} {A: ob 𝐂}: Fhom' F A ≡ F A := _Fidmap' A.
Definition Fcomp' {𝐂 𝐃} {F: ContravariantFunctor 𝐂 𝐃} {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C): Fhom' F (f \; g) ≡ Fhom' F g \; Fhom' F f := _Fcomp' _ _ _ f g. 

HB.factory Record IsContravariantFunctor' (𝐂 𝐃: PreCat) (F: ob 𝐂 -> ob 𝐃) := {
   Fhom': forall {A B: ob 𝐂}, (A ~> B) -> (F B ~> F A);
   Fhom'_eqv: forall {A B: ob 𝐂}, Proper (eqv ==> eqv) (@Fhom' A B);
   Fidmap': forall A: ob 𝐂, Fhom' A ≡ idmap (F A);
   Fcomp': forall {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C), Fhom' (g ∘ f) ≡ Fhom' f ∘ Fhom' g;
  }.
HB.builders Context 𝐂 𝐃 F of @IsContravariantFunctor' 𝐂 𝐃 F.
  HB.instance Definition _ := IsBarePreContravariantFunctor.Build _ _ F Fhom'.
  HB.instance Definition _ := IsPreContravariantFunctor'.Build _ _ F Fhom'_eqv.
  HB.instance Definition _ := IsContravariantFunctor.Build _ _ F Fidmap' Fcomp'.
HB.end.

(** rewriting tuple *)
Definition cats := (@Fidmap, @Fidmap', cats, @Fcomp, @Fcomp')%core.


(** * duality *)

Definition funcop1 {A B} (F: ob A -> ob B): ob (A^op) -> ob B := F.
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor 𝐂 𝐃) :=
  IsBarePreContravariantFunctor.Build 𝐂^op 𝐃 (funcop1 F) (fun _ _ f => Fhom F f).
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) :=
  IsPreContravariantFunctor'.Build 𝐂^op 𝐃 (funcop1 F) (fun A B f g fg => @Fhom_eqv _ _ F B A f g fg).
HB.instance Definition _ 𝐂 𝐃 (F: Functor 𝐂 𝐃) :=
  IsContravariantFunctor.Build 𝐂^op 𝐃 (funcop1 F) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _). 

HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor 𝐂 𝐃) :=
  IsBarePreFunctor.Build 𝐂^op 𝐃 (funcop1 F) (fun _ _ f => Fhom' F f).
HB.instance Definition _ 𝐂 𝐃 (F: PreContravariantFunctor 𝐂 𝐃) :=
  IsPreFunctor'.Build 𝐂^op 𝐃 (funcop1 F) (fun A B f g fg => @Fhom'_eqv _ _ F B A f g fg).
HB.instance Definition _ 𝐂 𝐃 (F: ContravariantFunctor 𝐂 𝐃) :=
  IsFunctor.Build 𝐂^op 𝐃 (funcop1 F) (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _). 

Definition funcop1' {A B} (F: ob (A^op) -> ob B): ob A -> ob B := F.
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor _ _) :=
  IsBarePreContravariantFunctor.Build 𝐂 𝐃 (funcop1' F) (fun _ _ f => Fhom F f).
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor _ _) :=
  IsPreContravariantFunctor'.Build 𝐂 𝐃 (funcop1' F) (fun A B f g fg => @Fhom_eqv _ _ F B A f g fg).
HB.instance Definition _ 𝐂 𝐃 (F: Functor _ _) :=
  IsContravariantFunctor.Build 𝐂 𝐃 (funcop1' F) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _). 

HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor _ _) :=
  IsBarePreFunctor.Build 𝐂 𝐃 (funcop1' F) (fun _ _ f => Fhom' F f).
HB.instance Definition _ 𝐂 𝐃 (F: PreContravariantFunctor _ _) :=
  IsPreFunctor'.Build 𝐂 𝐃 (funcop1' F) (fun A B f g fg => @Fhom'_eqv _ _ F B A f g fg).
HB.instance Definition _ 𝐂 𝐃 (F: ContravariantFunctor _ _) :=
  IsFunctor.Build 𝐂 𝐃 (funcop1' F) (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _). 

Definition funcop2 {A B} (F: ob A -> ob B): ob A -> ob (B^op) := F. 
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor 𝐂 𝐃) :=
  IsBarePreContravariantFunctor.Build 𝐂 𝐃^op (funcop2 F) (fun _ _ => Fhom F).
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) :=
  IsPreContravariantFunctor'.Build 𝐂 𝐃^op (funcop2 F) (@Fhom_eqv _ _ F).
HB.instance Definition _ 𝐂 𝐃 (F: Functor 𝐂 𝐃) :=
  IsContravariantFunctor.Build 𝐂 𝐃^op (funcop2 F) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _). 
HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor 𝐂 𝐃) :=
  IsBarePreFunctor.Build 𝐂 𝐃^op (funcop2 F) (fun _ _ => Fhom' F).
HB.instance Definition _ 𝐂 𝐃 (F: PreContravariantFunctor 𝐂 𝐃) :=
  IsPreFunctor'.Build 𝐂 𝐃^op (funcop2 F) (@Fhom'_eqv _ _ F).
HB.instance Definition _ 𝐂 𝐃 (F: ContravariantFunctor 𝐂 𝐃) :=
  IsFunctor.Build 𝐂 𝐃^op (funcop2 F) (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _). 

Definition funcop2' {A B} (F: ob A -> ob (B^op)): ob A -> ob B := F.
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor _ _) :=
  IsBarePreContravariantFunctor.Build 𝐂 𝐃 (funcop2' F) (fun _ _ f => Fhom F f).
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor _ _) :=
  IsPreContravariantFunctor'.Build 𝐂 𝐃 (funcop2' F) (@Fhom_eqv _ _ F).
HB.instance Definition _ 𝐂 𝐃 (F: Functor _ _) :=
  IsContravariantFunctor.Build 𝐂 𝐃 (funcop2' F) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _). 

HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor _ _) :=
  IsBarePreFunctor.Build 𝐂 𝐃 (funcop2' F) (fun _ _ f => Fhom' F f).
HB.instance Definition _ 𝐂 𝐃 (F: PreContravariantFunctor _ _) :=
  IsPreFunctor'.Build 𝐂 𝐃 (funcop2' F) (@Fhom'_eqv _ _ F).
HB.instance Definition _ 𝐂 𝐃 (F: ContravariantFunctor _ _) :=
  IsFunctor.Build 𝐂 𝐃 (funcop2' F) (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _). 

Check fun 𝐂 𝐃 (F: Functor 𝐂 𝐃) =>
        same (Functor _ _) (funcop2 (funcop1 F)) (funcop1 (funcop2 F)).
Check fun 𝐂 𝐃 (F: ContravariantFunctor 𝐂 𝐃) =>
        same (ContravariantFunctor _ _) (funcop2 (funcop1 F)) (funcop1 (funcop2 F)).
Check fun 𝐂 𝐃 (F: Functor 𝐂 𝐃) =>
        same (Functor _ _) (funcop2' (funcop2 F)) (funcop1' (funcop1 F)).

Definition funcop {A B} (F: ob A -> ob B): ob (A^op) -> ob (B^op) := funcop2 (funcop1 F). 
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor 𝐂 𝐃) :=
  BAREPREFUNCTOR.on (funcop F).
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) :=
  PREFUNCTOR.on (funcop F).
HB.instance Definition _ 𝐂 𝐃 (F: Functor 𝐂 𝐃) :=
  FUNCTOR.on (funcop F). 
HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor 𝐂 𝐃) :=
  BAREPRECONTRAVARIANTFUNCTOR.on (funcop F).
HB.instance Definition _ 𝐂 𝐃 (F: PreContravariantFunctor 𝐂 𝐃) :=
  PRECONTRAVARIANTFUNCTOR.on (funcop F).
HB.instance Definition _ 𝐂 𝐃 (F: ContravariantFunctor 𝐂 𝐃) :=
  CONTRAVARIANTFUNCTOR.on (funcop F).
(* TODO: faithful contravariant functors *)
HB.instance Definition _ 𝐂 𝐃 (F: FaithfulPreFunctor 𝐂 𝐃) :=
  IsFaithful.Build 𝐂^op 𝐃^op (funcop F) (fun A B => @Fhom_inj _ _ F B A).
HB.instance Definition _ 𝐂 𝐃 (F: FaithfulFunctor 𝐂 𝐃) := 
  IsFaithful.Build 𝐂^op 𝐃^op (funcop F) (fun A B => @Fhom_inj _ _ F B A). 


Definition funcop' {A B} (F: ob (A^op) -> ob (B^op)): ob A -> ob B := funcop1' (funcop2' F). 
HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: BarePreFunctor _ _) :=
  BAREPREFUNCTOR.on (@funcop' 𝐂 𝐃 F).
HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreFunctor _ _) :=
  PREFUNCTOR.on (@funcop' 𝐂 𝐃 F).
HB.instance Definition _ (𝐂 𝐃: PreCat) (F: Functor _ _) :=
  FUNCTOR.on (@funcop' 𝐂 𝐃 F). 
HB.instance Definition _ (𝐂 𝐃: BareQuiver) (F: BarePreContravariantFunctor _ _) :=
  BAREPRECONTRAVARIANTFUNCTOR.on (@funcop' 𝐂 𝐃 F).
HB.instance Definition _ (𝐂 𝐃: Quiver) (F: PreContravariantFunctor _ _) :=
  PRECONTRAVARIANTFUNCTOR.on (@funcop' 𝐂 𝐃 F).
HB.instance Definition _ (𝐂 𝐃: PreCat) (F: ContravariantFunctor _ _) :=
  CONTRAVARIANTFUNCTOR.on (@funcop' 𝐂 𝐃 F).
(* TODO: faithful contravariant functors *)

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
  Section s.
  Context {𝐂 𝐃: Cat} {F: ContravariantFunctor 𝐂 𝐃}.
  Fixpoint map' {A B} (u: hom_list A B): hom_list (F B) (F A) :=
    match u with
    | nil => nil
    | cons u v => snoc (map' v) (Fhom' F u)
    end.
  Lemma eval_map' {A B} (u: hom_list A B) : eval (map' u) ≡ Fhom' F (eval u).
  Proof.
    elim: u=>[/=|C D f u IH]; simpl map'. by rewrite Fidmap'.
    by rewrite eval_snoc eval_cons IH Fcomp'.
  Qed.
    
  Program Definition r_Fhom' {A B} (f: reified A B) :=
    reify (Fhom' F f) (map' (norm f)) _.
  Next Obligation. intros. by rewrite eval_map' normE. Qed.
  End s.
End HL.
Canonical HL.r_Fhom.
Canonical HL.r_Fhom'.


(** identity functor *)
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreFunctor.Build 𝐂 𝐂 idfun (fun A B => types_id).
HB.instance Definition _ (𝐂: PreCat) :=
  IsFunctor.Build 𝐂 𝐂 idfun (fun=> eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(** duality contravariant functors *)
HB.instance Definition _ (𝐂: BareQuiver) :=
  IsBarePreContravariantFunctor.Build 𝐂 𝐂^op obop morphop.
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreContravariantFunctor'.Build 𝐂 𝐂^op obop (fun _ _ _ _ H => H).
HB.instance Definition _ (𝐂: PreCat) :=
  IsContravariantFunctor.Build 𝐂 𝐂^op obop (fun=> eqv_refl) (fun _ _ _ _ _ => eqv_refl).
HB.instance Definition _ (𝐂: BareQuiver) :=
  IsBarePreContravariantFunctor.Build 𝐂^op 𝐂 obop' morphop'.
HB.instance Definition _ (𝐂: Quiver) :=
  IsPreContravariantFunctor'.Build 𝐂^op 𝐂 obop' (fun _ _ _ _ H => H).
HB.instance Definition _ (𝐂: PreCat) :=
  IsContravariantFunctor.Build 𝐂^op 𝐂 obop' (fun=> eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(** composition of functors *)
(** [catcomp] is the name for composing
    - either two functors
    - or a contravariant functor followed by a functor *)
(** [catcomp'] is the name for composing
    - either two contravariant functors
    - or a functor followed by a contravariant functor *)
Definition catcomp' {A B C} (F: ob A -> ob B) (G: ob B -> ob C) := catcomp (funcop2 F) (funcop1 G). 
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: BarePreFunctor 𝐂 𝐃} {G: BarePreFunctor 𝐃 𝐄} :=
  IsBarePreFunctor.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom F)).
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: PreFunctor 𝐂 𝐃} {G: PreFunctor 𝐃 𝐄} :=
  IsPreFunctor.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom F)).
Program Definition _comp_functor 𝐂 𝐃 𝐄 {F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  IsFunctor.Build 𝐂 𝐄 (catcomp F G) _ _.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fidmap. Qed.
Next Obligation. intros. cbn=>/=. by rewrite 2!Fcomp. Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_comp_functor 𝐂 𝐃 𝐄 F G.

(** composition of a contravariant functor and a functor *)
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: BarePreContravariantFunctor 𝐂 𝐃} {G: BarePreFunctor 𝐃 𝐄} :=
  IsBarePreContravariantFunctor.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom' F)).
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: PreContravariantFunctor 𝐂 𝐃} {G: PreFunctor 𝐃 𝐄} :=
  IsPreContravariantFunctor.Build 𝐂 𝐄 (catcomp F G) (fun _ _ => types_comp (Fhom G) (Fhom' F)).
Program Definition _comp_contravariantfunctor {𝐂 𝐃 𝐄: PreCat} {F: ContravariantFunctor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  IsContravariantFunctor.Build 𝐂 𝐄 (catcomp F G) _ _.
Next Obligation. intros. cbn=>/=. by rewrite Fidmap' Fidmap. Qed.
Next Obligation. intros. cbn=>/=. by rewrite Fcomp' Fcomp. Qed.
HB.instance Definition _ 𝐂 𝐃 𝐄 F G := @_comp_contravariantfunctor 𝐂 𝐃 𝐄 F G.

(** composition of contravariant functors *)
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: BarePreContravariantFunctor 𝐂 𝐃} {G: BarePreContravariantFunctor 𝐃 𝐄} :=
  BAREPREFUNCTOR.on (catcomp' F G). 
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: PreContravariantFunctor 𝐂 𝐃} {G: PreContravariantFunctor 𝐃 𝐄} :=
  PREFUNCTOR.on (catcomp' F G). 
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: ContravariantFunctor 𝐂 𝐃} {G: ContravariantFunctor 𝐃 𝐄} :=
  FUNCTOR.on (catcomp' F G).

(** composition of a functor and a contravariant functor *)
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: BarePreFunctor 𝐂 𝐃} {G: BarePreContravariantFunctor 𝐃 𝐄} :=
  BAREPRECONTRAVARIANTFUNCTOR.on (catcomp' F G).
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: PreFunctor 𝐂 𝐃} {G: PreContravariantFunctor 𝐃 𝐄} :=
  PRECONTRAVARIANTFUNCTOR.on (catcomp' F G).
HB.instance Definition _ 𝐂 𝐃 𝐄 {F: Functor 𝐂 𝐃} {G: ContravariantFunctor 𝐃 𝐄} :=
  CONTRAVARIANTFUNCTOR.on (catcomp' F G).

(** constant functor / contravariantfunctor *)
Definition cst {𝐂 𝐃: BareQuiver} (D: ob 𝐃) := fun of 𝐂 => D.
HB.instance Definition _ {𝐂: BareQuiver} {𝐃: BarePreCat} (D: 𝐃) :=
  IsBarePreFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (D: 𝐃) :=
  IsPreFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) :=
  IsFunctor.Build 𝐂 𝐃 (cst D) (fun=> eqv_refl)
    (fun _ _ _ _ _ => eqv_sym _ _ (compo1 idmap)).
HB.instance Definition _ {𝐂: BareQuiver} {𝐃: BarePreCat} (D: 𝐃) :=
  IsBarePreContravariantFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: Quiver} {𝐃: PreCat} (D: 𝐃) :=
  IsPreContravariantFunctor.Build 𝐂 𝐃 (cst D) (fun _ _ => const idmap).
HB.instance Definition _ {𝐂: PreCat} {𝐃: Cat} (D: 𝐃) :=
  IsContravariantFunctor.Build 𝐂 𝐃 (cst D) (fun=> eqv_refl)
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
Section s.
  Context {𝐂: PreCat} {𝐃: Cat} (F: ContravariantFunctor 𝐂 𝐃) (A B: ob 𝐂).
  Program Definition _contravariantfunctor_splitmono (i: SplitMono A B) := @HasLeftInverse.Build _ _ _ (Fhom' F i) (Fhom' F (i⁻¹)) _.
  Next Obligation. intros. by rewrite -Fcomp' invKr Fidmap'. Qed.
  HB.instance Definition _ i := @_contravariantfunctor_splitmono i.
  Program Definition _contravariantfunctor_splitepi (i: SplitEpi A B) := @HasRightInverse.Build _ _ _ (Fhom' F i) (Fhom' F (i⁻¹)) _.
  Next Obligation. intros. by rewrite -Fcomp' invKl Fidmap'. Qed.
  HB.instance Definition _ i := @_contravariantfunctor_splitepi i.
  HB.saturate Fhom'.
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
Definition functor_cst {𝐂 𝐃: Cat} (D: 𝐃): 𝐂 ≈> 𝐃 := cst D: Functor _ _.
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

(** contravariant naturality *)
#[primitive] HB.mixin Record IsNatural' {𝐂: BareQuiver} {𝐃: PreCat} (F G: BarePreContravariantFunctor 𝐂 𝐃) (n: TX F G) :=
  { #[canonical=no] natural': forall (X Y: ob 𝐂) (f: X ~> Y), n X ∘ Fhom' F f ≡ Fhom' G f ∘ n Y }.
#[short(type="NTX'")]
HB.structure Definition NATURAL' 𝐂 𝐃 F G :=
  { n of @IsNatural' 𝐂 𝐃 F G n }.
Arguments natural' {_ _ _ _} _ [_ _] _.

(* Definition morphop'' {𝐂: BareQuiver} {x y: ob 𝐂} (f: obop x ~> obop y): y ~> x := f. *)

Definition ntxop1 {𝐂 𝐃 F G} (n: @TX 𝐂 𝐃 F G): TX (funcop1 F) (funcop1 G) := n. 
Definition ntxop1' {𝐂 𝐃 F G} (n: TX F G): @TX 𝐂 𝐃 (funcop1' F) (funcop1' G) := n.
Definition ntxop2 {𝐂 𝐃 F G} (n: @TX 𝐂 𝐃 F G): TX (funcop2 G) (funcop2 F) := n (* fun X => morphop (n X) *).
Definition ntxop2' {𝐂 𝐃 F G} (n: TX F G): @TX 𝐂 𝐃 (funcop2' G) (funcop2' F) := n.
Definition ntxop {𝐂 𝐃 F G} (n: @TX 𝐂 𝐃 F G): TX (funcop G) (funcop F) := ntxop1 (ntxop2 n).
Definition ntxop' {𝐂 𝐃 F G} (n: TX F G): @TX 𝐂 𝐃 (funcop' G) (funcop' F) := ntxop2' (ntxop1' n).

HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor 𝐂 𝐃) (n: NTX F G) :=
  IsNatural'.Build 𝐂^op 𝐃 (funcop1 F) (funcop1 G) (ntxop1 n) (fun _ _ f => natural n f).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreContravariantFunctor _ _) (n: NTX' F G) :=
  IsNatural.Build 𝐂 𝐃 (funcop1' F) (funcop1' G) (ntxop1' n) (fun _ _ f => natural' n f).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor 𝐂 𝐃) (n: NTX F G) :=
  IsNatural'.Build 𝐂 𝐃^op (funcop2 G) (funcop2 F) (ntxop2 n) (fun _ _ f => eqv_sym _ _ (natural n f)).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreContravariantFunctor _ _) (n: NTX' F G) :=
  IsNatural.Build 𝐂 𝐃 (funcop2' G) (funcop2' F) (ntxop2' n) (fun _ _ f => eqv_sym _ _ (natural' n f)).

HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreContravariantFunctor 𝐂 𝐃) (n: NTX' F G) :=
  IsNatural.Build 𝐂^op 𝐃 (funcop1 F) (funcop1 G) (ntxop1 n) (fun _ _ f => natural' n f).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor _ _) (n: NTX F G) :=
  IsNatural'.Build 𝐂 𝐃 (funcop1' F) (funcop1' G) (ntxop1' n) (fun _ _ f => natural n f).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreContravariantFunctor 𝐂 𝐃) (n: NTX' F G) :=
  IsNatural.Build 𝐂 𝐃^op (funcop2 G) (funcop2 F) (ntxop2 n) (fun _ _ f => eqv_sym _ _ (natural' n f)).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor _ _) (n: NTX F G) :=
  IsNatural'.Build 𝐂 𝐃 (funcop2' G) (funcop2' F) (ntxop2' n) (fun _ _ f => eqv_sym _ _ (natural n f)).

HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor 𝐂 𝐃) (n: NTX F G) :=
  NATURAL.on (ntxop n).
HB.instance Definition _ (𝐂: BareQuiver) (𝐃: PreCat) (F G: BarePreContravariantFunctor _ _) (n: NTX' F G) :=
  NATURAL'.on (@ntxop' 𝐂 𝐃 F G n).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreContravariantFunctor 𝐂 𝐃) (n: NTX' F G) :=
  NATURAL'.on (ntxop n).
HB.instance Definition _ (𝐂: BareQuiver) (𝐃: PreCat) (F G: BarePreFunctor _ _) (n: NTX F G) :=
  NATURAL.on (@ntxop' 𝐂 𝐃 F G n).


(** setoid structure on natural transformations *)
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreFunctor 𝐂 𝐃) :=
  Setoid.copy (NTX F G) (kernel (@NATURAL.sort 𝐂 𝐃 F G)).
HB.instance Definition _ 𝐂 (𝐃: PreCat) (F G: BarePreContravariantFunctor 𝐂 𝐃) :=
  Setoid.copy (NTX' F G) (kernel (@NATURAL'.sort 𝐂 𝐃 F G)).

(** ** categories of (pre)functors and natural transformations *)
HB.instance Definition _  𝐂 (𝐃: PreCat) :=
  IsQuiver.Build (PreFunctor 𝐂 𝐃) (@NTX 𝐂 𝐃).
HB.instance Definition _  𝐂 (𝐃: PreCat) :=
  IsQuiver.Build (PreContravariantFunctor 𝐂 𝐃) (@NTX' 𝐂 𝐃).
HB.instance Definition _  𝐂 𝐃 :=
  IsQuiver.Build (Functor 𝐂 𝐃) (@NTX 𝐂 𝐃).
HB.instance Definition _  𝐂 𝐃 :=
  IsQuiver.Build (ContravariantFunctor 𝐂 𝐃) (@NTX' 𝐂 𝐃).

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
  IsPreAdjoint.Build 𝐂^op 𝐃 (funcop1 F) (funcop2 (adj F)).
HB.instance Definition _ {𝐂 𝐃: Type} (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐂 𝐃^op (funcop2 F) (funcop1 (adj F)).

HB.instance Definition _ {𝐂: Type} := IsPreAdjoint.Build 𝐂 𝐂 idfun idfun.
HB.instance Definition _ {𝐂: BareQuiver} := IsPreAdjoint.Build 𝐂 𝐂^op obop obop'.
HB.instance Definition _ {𝐂: BareQuiver} := IsPreAdjoint.Build 𝐂^op 𝐂 obop' obop.
HB.instance Definition _ {𝐂 𝐃 𝐄: Type} (F: PreAdjoint 𝐂 𝐃) (G: PreAdjoint 𝐃 𝐄) :=
  IsPreAdjoint.Build 𝐂 𝐄 (catcomp F G) (catcomp (adj G) (adj F)).
HB.instance Definition _ {𝐂 𝐃 𝐄: Type} (F: PreAdjoint 𝐂 𝐃) (G: PreAdjoint 𝐃 𝐄) :=
  PREADJOINT.on (catcomp' F G).

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

(** ** contravariants functors with an adjoint candidate *)

#[primitive] 
HB.mixin Record IsPreAdjointCF {𝐂 𝐃: PreCat} F of @PREADJOINT 𝐂 𝐃 F :=
  { #[canonical=no] _adj_contravariantfunctor: @CONTRAVARIANTFUNCTOR.axioms_ _ _ (adj F) }.
#[short(type="PreAdjointCF")]
HB.structure Definition PREADJOINTCF 𝐂 𝐃 := {F of @CONTRAVARIANTFUNCTOR 𝐂 𝐃 F & IsPreAdjointCF _ _ F & IsPreAdjoint _ _ F}.
HB.instance Definition _ 𝐂 𝐃 F := @_adj_contravariantfunctor 𝐂 𝐃 F. 

HB.factory Record IsPreAdjointCF' 𝐂 𝐃 F of @CONTRAVARIANTFUNCTOR 𝐂 𝐃 F :=
  { adj: ContravariantFunctor 𝐃 𝐂 }.
HB.builders Context 𝐂 𝐃 F of IsPreAdjointCF' 𝐂 𝐃 F. 
  HB.instance Definition _ := IsPreAdjoint.Build 𝐂 𝐃 F adj. 
  HB.instance Definition _ := IsPreAdjointCF.Build 𝐂 𝐃 F (CONTRAVARIANTFUNCTOR.class adj).
HB.end.

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointCF 𝐂 𝐃) :=
  IsPreAdjointCF'.Build 𝐃 𝐂 (adj F) F.


HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointF'.Build 𝐂^op 𝐃^op (funcop F) (funcop (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointCF 𝐂 𝐃) :=
  IsPreAdjointCF'.Build 𝐂^op 𝐃^op (funcop F) (funcop (adj F)).

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointCF 𝐂 𝐃) :=
  IsPreAdjointF'.Build 𝐂^op 𝐃 (funcop1 F) (funcop2 (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointCF'.Build 𝐂^op 𝐃 (funcop1 F) (funcop2 (adj F)).

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointCF 𝐂 𝐃) :=
  IsPreAdjointF'.Build 𝐂 𝐃^op (funcop2 F) (funcop1 (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointCF'.Build 𝐂 𝐃^op (funcop2 F) (funcop1 (adj F)).

HB.instance Definition _ 𝐂 := IsPreAdjointF'.Build 𝐂 𝐂 idfun idfun.
HB.instance Definition _ 𝐂 := IsPreAdjointCF'.Build 𝐂 𝐂^op obop obop'.
HB.instance Definition _ {𝐂: PreCat} := IsPreAdjointCF'.Build 𝐂^op 𝐂 obop' obop.

HB.instance Definition _ 𝐂 𝐃 𝐄 (F: PreAdjointF 𝐂 𝐃) (G: PreAdjointF 𝐃 𝐄) :=
  IsPreAdjointF'.Build 𝐂 𝐄 (catcomp F G) (catcomp (adj G) (adj F)).
HB.instance Definition _ 𝐂 𝐃 𝐄 (F: PreAdjointCF 𝐂 𝐃) (G: PreAdjointF 𝐃 𝐄) :=
  IsPreAdjointCF'.Build 𝐂 𝐄 (catcomp F G) (catcomp' (adj G) (adj F)).
HB.instance Definition _ 𝐂 𝐃 𝐄 (F: PreAdjointCF 𝐂 𝐃) (G: PreAdjointCF 𝐃 𝐄) :=
  IsPreAdjointF'.Build 𝐂 𝐄 (catcomp' F G) (catcomp' (adj G) (adj F)).
HB.instance Definition _ 𝐂 𝐃 𝐄 (F: PreAdjointF 𝐂 𝐃) (G: PreAdjointCF 𝐃 𝐄) :=
  IsPreAdjointCF'.Build 𝐂 𝐄 (catcomp' F G) (catcomp (adj G) (adj F)).



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

Definition op12 {𝐂 𝐃: PreCat} {F: PreContravariantFunctor 𝐂 𝐃} {G: PreContravariantFunctor 𝐃 𝐂}
  (FG: type (funcop1 F) (funcop2 G)):
  type (funcop1 G) (funcop2 F) := 
  mk
    (ntxop (counit FG): NTX _ _)
    (ntxop' (unit FG): NTX _ _)
    (unit_counit_r_at FG)
    (unit_counit_l_at FG).

Definition op21 {𝐂 𝐃: PreCat} {F: PreContravariantFunctor 𝐂 𝐃} {G: PreContravariantFunctor 𝐃 𝐂}
  (FG: type (funcop2 F) (funcop1 G)):
  type (funcop2 G) (funcop1 F) :=
  mk
    (ntxop' (counit FG): NTX _ _)
    (ntxop (unit FG): NTX _ _)
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

(** ** contravariant left adjoints (= contravariant functors with a right adjoint) *)

#[primitive] HB.mixin Record IsCLeftAdjoint 𝐂 𝐃 F of @PREADJOINTCF 𝐂 𝐃 F :=
  { #[canonical=no] cladjP: Adj.type (funcop1 F) (funcop2 (adj F)) }.
#[short(type="CLeftAdjoint")]
HB.structure Definition CLEFTADJOINT 𝐂 𝐃 := {F of IsCLeftAdjoint 𝐂 𝐃 F & }.

(** ** contravariant right adjoints (= contravariant functors with a left adjoint) *)

#[primitive] HB.mixin Record IsCRightAdjoint 𝐂 𝐃 F of @PREADJOINTCF 𝐂 𝐃 F :=
  { #[canonical=no] cradjP: Adj.type (funcop2 (adj F)) (funcop1 F) }.
#[short(type="CRightAdjoint")]
HB.structure Definition CRIGHTADJOINT 𝐂 𝐃 := {F of IsCRightAdjoint 𝐂 𝐃 F & }.

(** ** contravariant adjoint equivalences (= contravariant functors which are both left and right adjoints) *)

#[short(type="CAdjointEquivalence")]
HB.structure Definition CADJOINTEQUIVALENCE 𝐂 𝐃 :=
  {F of @CLEFTADJOINT 𝐂 𝐃 F & @CRIGHTADJOINT 𝐂 𝐃 F }.


(** * adjunction instances *)

(** ** duality instances *)

(* LA <-adj-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊣ 𝐃) :=
  IsRightAdjoint.Build 𝐃 𝐂 (adj F) ladjP.
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊢ 𝐃) :=
  IsLeftAdjoint.Build 𝐃 𝐂 (adj F) radjP.

(* CLA <-adj-> CLA *)
HB.instance Definition _ 𝐂 𝐃 (F: CLeftAdjoint 𝐂 𝐃) :=
  IsCLeftAdjoint.Build 𝐃 𝐂 (adj F) (Adj.op12 cladjP).

(* CRA <-adj-> CRA *)
HB.instance Definition _ 𝐂 𝐃 (F: CRightAdjoint 𝐂 𝐃) :=
  IsCRightAdjoint.Build 𝐃 𝐂 (adj F) (Adj.op21 cradjP).

(* * obtained as a corollary below *)
(* HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊣ 𝐃) := *)
(*   IsRightAdjoint.Build 𝐂^op 𝐃^op (funcop F) (Adj.op ladjP). *)
(* HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊢ 𝐃) := *)
(*   IsLeftAdjoint.Build 𝐂^op 𝐃^op (funcop F) (Adj.op radjP). *)

(* LA <-funcop1-> CLA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊣ 𝐃) :=
  IsCLeftAdjoint.Build 𝐂^op 𝐃 (funcop1 F) (Adj.op12 (Adj.op (@ladjP _ _ F))).
HB.instance Definition _ 𝐂 𝐃 (F: CLeftAdjoint 𝐂 𝐃) :=
  IsLeftAdjoint.Build 𝐂^op 𝐃 (funcop1 F) cladjP.
  
(* RA <-funcop1-> CRA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊢ 𝐃) :=
  IsCRightAdjoint.Build 𝐂^op 𝐃 (funcop1 F) (Adj.op21 (Adj.op (@radjP _ _ F))).
HB.instance Definition _ 𝐂 𝐃 (F: CRightAdjoint 𝐂 𝐃) :=
  IsRightAdjoint.Build 𝐂^op 𝐃 (funcop1 F) cradjP.

(* LA <-funcop2-> CRA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊣ 𝐃) :=
  IsCRightAdjoint.Build 𝐂 𝐃^op (funcop2 F) (Adj.op ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: CRightAdjoint 𝐂 𝐃) :=
  IsLeftAdjoint.Build 𝐂 𝐃^op (funcop2 F) (Adj.op21 cradjP).

(* RA <-funcop2-> CLA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊢ 𝐃) :=
  IsCLeftAdjoint.Build 𝐂 𝐃^op (funcop2 F) (Adj.op radjP).
HB.instance Definition _ 𝐂 𝐃 (F: CLeftAdjoint 𝐂 𝐃) :=
  IsRightAdjoint.Build 𝐂 𝐃^op (funcop2 F) (Adj.op12 cladjP).

(* LA <-funcop-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊣ 𝐃) :=
  RIGHTADJOINT.on (funcop F).
HB.instance Definition _ 𝐂 𝐃 (F: 𝐂 ⊢ 𝐃) :=
  LEFTADJOINT.on (funcop F).

(** ** identity adjunctions *)
HB.instance Definition _ (𝐂: Cat) := IsLeftAdjoint.Build 𝐂 𝐂 idfun Adj.id.
HB.instance Definition _ (𝐂: Cat) := IsRightAdjoint.Build 𝐂 𝐂 idfun Adj.id.

(** ** composing adjunctions  *)
(* catcomp *)
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: LeftAdjoint 𝐂 𝐃) (G: LeftAdjoint 𝐃 𝐄) :=
  IsLeftAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp ladjP ladjP).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: CLeftAdjoint 𝐂 𝐃) (G: LeftAdjoint 𝐃 𝐄) :=
  IsCLeftAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp cladjP ladjP).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: RightAdjoint 𝐂 𝐃) (G: RightAdjoint 𝐃 𝐄) :=
  IsRightAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp radjP radjP).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: CRightAdjoint 𝐂 𝐃) (G: RightAdjoint 𝐃 𝐄) :=
  IsCRightAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp radjP cradjP).
(* catcomp' *)
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: CRightAdjoint 𝐂 𝐃) (G: CLeftAdjoint 𝐃 𝐄) :=
 LEFTADJOINT.on (catcomp' F G).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: CLeftAdjoint 𝐂 𝐃) (G: CRightAdjoint 𝐃 𝐄) :=
 RIGHTADJOINT.on (catcomp' F G).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: RightAdjoint 𝐂 𝐃) (G: CLeftAdjoint 𝐃 𝐄) :=
 CLEFTADJOINT.on (catcomp' F G).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: LeftAdjoint 𝐂 𝐃) (G: CRightAdjoint 𝐃 𝐄) :=
 CRIGHTADJOINT.on (catcomp' F G).


(** ** duality (contravariant) adjunction  *)
HB.instance Definition _ (𝐂: Cat) := @IsCLeftAdjoint.Build 𝐂 𝐂^op obop Adj.id.
HB.instance Definition _ (𝐂: Cat) := @IsCRightAdjoint.Build 𝐂 𝐂^op obop Adj.id.
HB.instance Definition _ (𝐂: Cat) := @IsCLeftAdjoint.Build 𝐂^op 𝐂 obop' Adj.id.
HB.instance Definition _ (𝐂: Cat) := @IsCRightAdjoint.Build 𝐂^op 𝐂 obop' Adj.id.


(* TOFIX: declarations below are no-ops *)
HB.saturate adj. 
HB.saturate funcop. 
HB.saturate catcomp. 
HB.saturate catcomp'. 
(* we emulate them using the following asymmetric declarations *)
HB.instance Definition _ C D (F: AdjointEquivalence C D) := LEFTADJOINT.on (adj F).
HB.instance Definition _ C D (F: AdjointEquivalence C D) := LEFTADJOINT.on (funcop F).
HB.instance Definition _ (C D E: Cat) (F: AdjointEquivalence C D) (G: AdjointEquivalence D E) := LEFTADJOINT.on (catcomp F G).
HB.instance Definition _ (C D E: Cat) (F: CAdjointEquivalence C D) (G: CAdjointEquivalence D E) := LEFTADJOINT.on (catcomp' F G).

Check fun (C D: Cat) (F: AdjointEquivalence C D) => adj F: AdjointEquivalence D C. 
Check fun (C D: Cat) (F: AdjointEquivalence C D) => funcop F: AdjointEquivalence (C^op) (D^op). 
Check fun (C: Cat) (F G: AdjointEquivalence C C) => catcomp F G: AdjointEquivalence C C. 
Check fun (C: Cat) (F G: CAdjointEquivalence C C) => catcomp' F G: AdjointEquivalence C C. 

(** ** adjoint equivalence of C and C^op^op *)
Definition opI {𝐂: BareQuiver}: ob 𝐂 -> ob (𝐂^op^op) := catcomp' obop obop.
HB.instance Definition _ (𝐂: Cat) := ADJOINTEQUIVALENCE.on (@opI 𝐂). 


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
Lemma cradj_initial (𝐂 𝐃: Cat) (F: CRightAdjoint 𝐂 𝐃) (A: ob 𝐂) (H: initial A): terminal (F A).
Proof. exact: (ladj_initial (funcop2 F) H). Defined.
Lemma cladj_terminal (𝐂 𝐃: Cat) (F: CLeftAdjoint 𝐂 𝐃) (A: ob 𝐂) (H: terminal A): initial (F A).
Proof. exact: (ladj_initial (funcop1 F) H). Defined.
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
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: CRightAdjoint 𝐂 𝐃) (A: Initial 𝐂) :=
  IsTerminal.Build 𝐃 (F A) (cradj_initial F initialP).
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: CLeftAdjoint 𝐂 𝐃) (A: Terminal 𝐂) :=
  IsInitial.Build 𝐃 (F A) (cladj_terminal F terminalP).

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
