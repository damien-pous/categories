(** * Functors and natural transformations *)

Require Export morphisms.
Require Import cast.

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
  IsPreFunctor.Build 𝐂 𝐄 (types_comp G F) (fun _ _ => types_comp (Fhom G) (Fhom F)).
Program Definition _comp_functor {𝐂 𝐃 𝐄: PreCat} {F: Functor 𝐂 𝐃} {G: Functor 𝐃 𝐄} :=
  IsFunctor.Build 𝐂 𝐄 (types_comp G F) _ _.
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

#[projections(primitive=no)]
Record functor_eqv {𝐂} {𝐃: Cat} (F G: Functor 𝐂 𝐃): Prop := { _: F ≈ G }. 

#[local] Instance Equivalence_functor_eqv {𝐂} {𝐃: Cat}: Equivalence (@functor_eqv 𝐂 𝐃). 
Proof.
  split.
  -- intro h. split. apply: iso_refl.
  -- intros F G [i]. split. exact: iso_sym. 
  -- intros F G H [i] [j]. split. apply: iso_trans; eassumption.
Qed.
HB.instance Definition _ {𝐂}{𝐃: Cat} := isSetoid.Build (Functor 𝐂 𝐃) _.

(* waiting for universe polymorphism, we cannot declare the following instance *)
(*TMP-UNIV
HB.instance Definition _ := IsQuiver.Build Cat Functor. 
*)
(* meanwhile, we use the following notation for functors; later we will replace it with "~>" *)
Notation "F ≈> G" := (Functor F G): cat_scope.
Definition functor_id {𝐂: Cat}: 𝐂 ≈> 𝐂 := idfun: Functor 𝐂 𝐂.
Definition functor_comp {𝐂 𝐃 𝐄: Cat} (F: 𝐂 ≈> 𝐃) (G: 𝐃 ≈> 𝐄): 𝐂 ≈> 𝐄 := types_comp G F: Functor _ _.
Definition functor_cst {𝐂 𝐃: Cat} (D: 𝐃): 𝐂 ≈> 𝐃 := cst D: Functor _ _.
(*TMP-UNIV
HB.instance Definition _ := IsPreCat.Build Cat (@functor_id) (@functor_comp). 
*)


Lemma iso_ntx_alt 𝐂 (𝐃: Cat) (F G: 𝐂 ≈> 𝐃) (i: F ≈ G) A B (f: A ~> B):
  Fhom G f ≡ i B ∘ Fhom F f ∘ (i A)⁻¹.
Proof. rewrite natural -compoA invKl. cat. Qed.

Lemma iso_ntx_eqv 𝐂 (𝐃: Cat) (F G: 𝐂 ≈> 𝐃) (i: F ≈ G) A B (f g: A ~> B):
  Fhom F f ≡ Fhom F g -> Fhom G f ≡ Fhom G g.
Proof. rewrite 2!(iso_ntx_alt i). by move=>->. Qed.

(* Check fun {𝐂 𝐃: Cat} (F G: 𝐂 ≈> 𝐃) (i: F ≈ G) (X: 𝐂) => unify (i⁻¹ X)  (i X)⁻¹. *)

Definition ntx_comp'_ 𝐂 𝐃 {𝐄: PreCat} {F G: PreFunctor 𝐂 𝐃} {F' G': PreFunctor 𝐃 𝐄}
  (k: forall X, F X ~> G X) (h: forall X, F' X ~> G' X): forall X, (types_comp F' F) X ~> (types_comp G' G) X :=
  (fun X => h _ ∘ Fhom _ (k _)).
Arguments ntx_comp'_ {_ _ _ _ _ _ _} _ _ _/. 
Program Definition _ntx_comp'_natural 𝐂 𝐃 (𝐄: Cat) (F G: 𝐂 ≈> 𝐃) (F' G': 𝐃 ≈> 𝐄)
  (k: F ~> G) (h: F' ~> G') := IsNatural.Build 𝐂 𝐄 (types_comp F' F) (types_comp G' G) (ntx_comp'_ k h) _.
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
Notation "h ⊚ k" := (ntx_comp' k h): cat_scope.

Section strict.
Context {𝐂 𝐃 𝐄: Cat}.
Lemma endo_exchange {F G H: 𝐂 ≈> 𝐃} {F' G' H': 𝐃 ≈> 𝐄}
  (i: F ~> G) (j: G ~> H)
  (i': F' ~> G') (j': G' ~> H'):
  (j'⊚j) ∘ (i'⊚i) ≡ (j'∘i') ⊚ (j∘i).
Proof.
  intro X; cbn.
  rewrite -!compoA. apply comp_eqv=>//.
  normalise. by rewrite natural.
Qed.

Lemma ntx_id_comp {F: 𝐂 ≈> 𝐃} {G: 𝐃 ≈> 𝐄}:
  (*TMP-UNIV: functor_comp -> ∘ once we have Cat:Cat  *)
  idmap (functor_comp F G) ≡ idmap G ⊚ idmap F.
Proof. intro X; cbn. by rewrite !cats. Qed.

Lemma ntx_comp'_eqv {F G: 𝐂 ≈> 𝐃} {F' G': 𝐃 ≈> 𝐄}:
  Proper (eqv ==> eqv ==> eqv) (@ntx_comp' _ _ _ F G F' G').
Proof. intros i i' ii j j' jj X. by rewrite /= (ii _) (jj _). Qed.

Lemma functor_comp_eqv:
  Proper (eqv ==> eqv ==> eqv) (@functor_comp 𝐂 𝐃 𝐄).
Proof.
  intros F G [i] F' G' [j]. split.  
  apply: (mk_iso' (j⊚ i) (j⁻¹⊚i⁻¹) _ _).
  rewrite endo_exchange.
  etransitivity. exact: (ntx_comp'_eqv (invKl i) (invKl j)). by rewrite -ntx_id_comp. 
  rewrite endo_exchange.
  etransitivity. exact: (ntx_comp'_eqv (invKr i) (invKr j)). by rewrite -ntx_id_comp. 
Qed.
End strict.

(*TMP-UNIV 
Program Definition _cat_cat := IsCat.Build Cat _ _ _ _.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. intros. exact: functor_comp_eqv. Qed.
HB.instance Definition _ := _cat_cat.
*)
