(** * adjunctions *)

Require Export functor.
Require Import arewrite.

Local Open Scope cat_scope.

(** ** adjunctions *)

Module Adj.
  Record adjunction (𝐂 𝐃: PreCat) (F: PreFunctor 𝐂 𝐃) (G: PreFunctor 𝐃 𝐂) :=
    mk {
        unit: NTX idfun (catcomp F G);
        counit: NTX (catcomp G F) idfun;
        (* unit: functor_id ~> functor_comp F G; *)
        (* counit: functor_comp G F ~> functor_id; *)
        unit_counit_l_at: forall a, Fhom F (unit a) \; counit (F a) ≡ F a;
        unit_counit_r_at: forall b, unit (G b) \; Fhom G (counit b) ≡ G b;
        (* unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _; *)
        (* unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _; *)
    }.
  Infix "⊣" := adjunction (at level 79): cat_scope.
  Arguments adjunction: clear implicits.
  Arguments mk {_ _ _ _} &.
  
  Section theory.
  Context {𝐂 𝐃: Cat} {F G: Functor _ _} (s: adjunction 𝐂 𝐃 F G).
  
  Definition unit': functor_id ~> functor_comp F G := unit s. (* abbreviation? *)
  Definition counit': functor_comp G F ~> functor_id := counit s. (* abbreviation? *)
  Lemma unit_counit_l: idmap ⊚ unit s \; counit s ⊚ idmap ≡ ntx_id _.
  Proof. move=>a. move:(unit_counit_l_at s a)=>/=. by rewrite !cats. Qed.
  Lemma unit_counit_r: unit s ⊚ idmap \; idmap ⊚ counit s ≡ ntx_id _.
  Proof. move=>b. move:(unit_counit_r_at s b)=>/=. by rewrite !cats. Qed.

  Section s.
    Context {a: ob 𝐂} {b: ob 𝐃}.
    
    Definition up (f: F a ~> b): a ~> G b :=
      Fhom G f ∘ unit s a.
    Definition dn (f: a ~> G b): F a ~> b :=
      counit s b ∘ Fhom F f. 

    #[export] Instance up_eqv: Proper (eqv ==> eqv) up.
    Proof. move=>f f' ff. rewrite/up. apply:comp_eqv=>//. exact/Fhom_eqv. Qed.
    HB.instance Definition _ := isExtensional.Build _ _ _ up_eqv. 
    
    #[export] Instance dn_eqv: Proper (eqv ==> eqv) dn.
    Proof. move=>f f' ff. rewrite/dn. apply:comp_eqv=>//. exact/Fhom_eqv. Qed.
    HB.instance Definition _ := isExtensional.Build _ _ _ dn_eqv.
    
    Lemma dn_up (f: F a ~> b): dn (up f) ≡ f.
    Proof.
      rewrite /dn/up/=Fcomp.
      rewrite compoA (natural (counit s)). 
      rewrite -compoA (unit_counit_l_at s).
      cat. 
    Qed.
    
    Lemma up_inj: injective up.
    Proof. move=>f g H. rewrite -(dn_up f) -(dn_up g). exact/dn_eqv. Qed.
    
    Lemma up_dn (f: a ~> G b): up (dn f) ≡ f.
    Proof.
      rewrite /dn/up/=Fcomp.
      rewrite -compoA -(natural (unit s)). 
      rewrite compoA (unit_counit_r_at s).
      cat. 
    Qed.
    
    Lemma dn_inj: injective dn.
    Proof. move=>f g H. rewrite -(up_dn f) -(up_dn g). exact/up_eqv. Qed.
    
  End s.

  (** left adjoints preserve initial objects *)
  Theorem preserve_initial (a: ob 𝐂) (H: initial a): initial (F a).
  Proof. move=>b. apply: (unique_impl dn up_inj). exact/H. Defined.

  (** right adjoints preserve terminal objects *)
  Theorem preserve_terminal (b: ob 𝐃) (H: terminal b): terminal (G b).
  Proof. move=>a. apply: (unique_impl up dn_inj). exact/H. Defined.
  
  End theory.
  
  Program Definition id {𝐂: Cat}: adjunction 𝐂 𝐂 idfun idfun :=
    mk (ntx_id _) (ntx_id _) _ _.
  Next Obligation. cbn=>*. cat. Qed.
  Next Obligation. cbn=>*. cat. Qed.

  Program Definition comp {𝐂 𝐃 𝐄: Cat} {F F' G G': Functor _ _}
    (FF: adjunction 𝐂 𝐃 F F')
    (GG: adjunction 𝐃 𝐄 G G'):
    catcomp F G ⊣ catcomp G' F' :=
    mk
      (unit' FF \; idmap ⊚ unit' GG ⊚ idmap)
      (idmap ⊚ counit' FF ⊚ idmap \; counit' GG) _ _.
  Admit Obligations.
  (* Next Obligation. move=>𝐂 𝐃 𝐄 F F' G G' FF GG A/=. rewrite !cats. Admitted.  *)
  (* Next Obligation. move=>𝐂 𝐃 𝐄 F F' G G' FF GG B/=. rewrite !cats. Admitted.  *)

  Definition op {𝐂 𝐃 F G} (FG: adjunction 𝐂 𝐃 F G): funcop G ⊣ funcop F :=
    mk
      (ntxop (counit FG): NTX _ _)
      (ntxop (unit FG): NTX _ _)
      (unit_counit_r_at FG)
      (unit_counit_l_at FG).

  Definition op' {𝐂 𝐃 F G} (FG: F ⊣ G): adjunction 𝐂 𝐃 (funcop' G) (funcop' F) :=
    mk
      (ntxop' (counit FG): NTX _ _)
      (ntxop' (unit FG): NTX _ _)
      (unit_counit_r_at FG)
      (unit_counit_l_at FG).

End Adj.
Definition adjunction := Adj.adjunction.
Infix "⊣" := adjunction (at level 79): cat_scope.

(** * HB inferrence *)

(** ** functions with an adjoint candidate (either left or right, or both) *)

#[primitive] 
HB.mixin Record IsPreAdjoint {𝐂 𝐃} (F: ob 𝐂 -> ob 𝐃) :=
  { #[canonical=no] adj: ob 𝐃 -> ob 𝐂 }.
#[short(type="PreAdjoint")]
HB.structure Definition PREADJOINT 𝐂 𝐃 := {F of IsPreAdjoint 𝐂 𝐃 F }.
Arguments adj {_ _} _.

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build 𝐃 𝐂 (@adj 𝐂 𝐃 F) F.

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjoint 𝐂 𝐃) :=
  IsPreAdjoint.Build _ _ (funcop F) (funcop (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjoint _ _) :=
  IsPreAdjoint.Build 𝐂 𝐃 (funcop' F) (funcop' (adj F)).

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjoint 𝐂 _) :=
  IsPreAdjoint.Build _ 𝐃 (funcop12 F) (funcop21 (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjoint _ 𝐃) :=
  IsPreAdjoint.Build 𝐂 _ (funcop21 F) (funcop12 (adj F)).

HB.instance Definition _ 𝐂 :=
  IsPreAdjoint.Build 𝐂 𝐂 idfun idfun.

HB.instance Definition _ 𝐂 𝐃 𝐄 (F: PreAdjoint 𝐂 𝐃) (G: PreAdjoint 𝐃 𝐄) :=
  IsPreAdjoint.Build 𝐂 𝐄 (catcomp F G) (catcomp (adj G) (adj F)).

(** ** functors with an adjoint candidate (either left or right, or both) *)

#[primitive] 
HB.mixin Record IsPreAdjointF' {𝐂 𝐃: PreCat} F of @PREADJOINT 𝐂 𝐃 F :=
  { #[canonical=no] _adj_functor: @FUNCTOR.axioms_ _ _ (adj F) }.
#[short(type="PreAdjointF")]
HB.structure Definition PREADJOINTF 𝐂 𝐃 := {F of @FUNCTOR 𝐂 𝐃 F & IsPreAdjointF' _ _ F & IsPreAdjoint _ _ F}.
HB.instance Definition _ 𝐂 𝐃 F := @_adj_functor 𝐂 𝐃 F. 

HB.factory Record IsPreAdjointF 𝐂 𝐃 F of @FUNCTOR 𝐂 𝐃 F :=
  { adj: Functor 𝐃 𝐂 }.
HB.builders Context 𝐂 𝐃 F of IsPreAdjointF 𝐂 𝐃 F. 
  HB.instance Definition _ := IsPreAdjoint.Build 𝐂 𝐃 F adj. 
  HB.instance Definition _ := IsPreAdjointF'.Build 𝐂 𝐃 F (FUNCTOR.class adj).
HB.end.

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointF.Build 𝐃 𝐂 (adj F) F.

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 𝐃) :=
  IsPreAdjointF.Build _ _ (funcop F) (funcop (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF _ _) :=
  IsPreAdjointF.Build 𝐂 𝐃 (funcop' F) (funcop' (adj F)).

HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF _ 𝐃) :=
  IsPreAdjointF.Build 𝐂 _ (funcop12 F) (funcop21 (adj F)).
HB.instance Definition _ 𝐂 𝐃 (F: PreAdjointF 𝐂 _) :=
  IsPreAdjointF.Build _ 𝐃 (funcop21 F) (funcop12 (adj F)).

HB.instance Definition _ 𝐂 :=
  IsPreAdjointF.Build 𝐂 𝐂 idfun idfun.

HB.instance Definition _ 𝐂 𝐃 𝐄 (F: PreAdjointF 𝐂 𝐃) (G: PreAdjointF 𝐃 𝐄) :=
  IsPreAdjointF.Build 𝐂 𝐄 (catcomp F G) (catcomp (adj G) (adj F)).


(** ** functors with a left/right adjoint *)

#[primitive] 
HB.mixin Record IsLeftAdjoint {𝐂 𝐃: PreCat} F of @PREADJOINTF 𝐂 𝐃 F :=
  { #[canonical=no] ladjP: F ⊣ adj F; }.
#[short(type="LeftAdjoint")]
HB.structure Definition LEFTADJOINT 𝐂 𝐃 := {F of IsLeftAdjoint 𝐂 𝐃 F & }.

#[primitive] 
HB.mixin Record IsRightAdjoint {𝐂 𝐃: PreCat} F of @PREADJOINTF 𝐂 𝐃 F :=
  { #[canonical=no] radjP: adj F ⊣  F }.
#[short(type="RightAdjoint")]
HB.structure Definition RIGHTADJOINT 𝐂 𝐃 := {F of IsRightAdjoint 𝐂 𝐃 F & }.

(** ** adjoint equivalences *)

#[short(type="AdjointEquivalence")]
HB.structure Definition ADJOINTEQUIVALENCE 𝐂 𝐃 := {F of @LEFTADJOINT 𝐂 𝐃 F & @RIGHTADJOINT 𝐂 𝐃 F }.


(** * adjunction instances *)

(** ** duality instances *)

(* LA <-adj-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: LeftAdjoint 𝐂 𝐃) :=
  IsRightAdjoint.Build 𝐃 𝐂 (adj F) ladjP.
HB.instance Definition _ 𝐂 𝐃 (F: RightAdjoint 𝐂 𝐃) :=
  IsLeftAdjoint.Build 𝐃 𝐂 (adj F) radjP.

(* LA <-funcop-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: LeftAdjoint 𝐂 𝐃) :=
  IsRightAdjoint.Build _ _ (funcop F) (Adj.op ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: RightAdjoint 𝐂 𝐃) :=
  IsLeftAdjoint.Build _ _ (funcop F) (Adj.op radjP).
HB.instance Definition _ 𝐂 𝐃 (F: LeftAdjoint _ _) :=
  IsRightAdjoint.Build 𝐂 𝐃 (funcop' F) (Adj.op' ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: RightAdjoint _ _) :=
  IsLeftAdjoint.Build 𝐂 𝐃 (funcop' F) (Adj.op' radjP).

(* TODO: funcop12 *)

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


(** * binding properties of adjunctions to HB's inferrence *)

Module ladj.
Section binding.
Context {𝐂 𝐃: Cat} (F: LeftAdjoint 𝐂 𝐃).

Definition unit: NTX idfun (catcomp F (adj F)) := Adj.unit ladjP.
Definition counit: NTX (catcomp (adj F) F) idfun := Adj.counit ladjP.
Definition unit_counit_l_at: forall a, Fhom F (unit a) \; counit (F a) ≡ F a := Adj.unit_counit_l_at ladjP.
Definition unit_counit_r_at: forall b, unit (adj F b) \; Fhom (adj F) (counit b) ≡ adj F b := Adj.unit_counit_r_at ladjP.
Definition unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _ := Adj.unit_counit_l ladjP.
Definition unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _ := Adj.unit_counit_r ladjP.

Definition up: forall a b, (F a ~> b) -> (a ~> adj F b) := @Adj.up _ _ _ _ (@ladjP _ _ F).
Definition dn: forall a b, (a ~> adj F b) -> (F a ~> b) := @Adj.dn _ _ _ _ (@ladjP _ _ F).

Lemma preserve_initial A: initial A -> initial (F A).
Proof. exact:(Adj.preserve_initial ladjP). Defined.

Lemma preserve_Initial (A: Initial 𝐂): initial (F A).
Proof. exact:(preserve_initial initialP). Defined.

End binding.
End ladj.

(* TOFIX: wrongly detected forgetful inheritance (two distinct hierarchies) *)
#[non_forgetful_inheritance]
HB.instance Definition _ 𝐂 𝐃 F A := IsInitial.Build _ _ (@ladj.preserve_Initial 𝐂 𝐃 F A).

Check fun (𝐂 𝐃: Cat) (F: LeftAdjoint 𝐂 𝐃) (A: Initial 𝐂) => F A: Initial _.
(* TOFIX: HB does not register the required things...
   use a tag above to adhere to its discipline? *)
Fail Check fun (𝐂 𝐃: Cat) (F: AdjointEquivalence 𝐂 𝐃) (A: Initial 𝐂) => F A: Initial _.


Module radj.
Section binding.
Context {𝐂 𝐃: Cat} (F: RightAdjoint 𝐂 𝐃).

Definition unit: NTX idfun (catcomp (adj F) F) := Adj.unit radjP.
Definition counit: NTX (catcomp F (adj F)) idfun := Adj.counit radjP.
Definition unit_counit_l_at: forall a, Fhom (adj F) (unit a) \; counit (adj F a) ≡ adj F a := Adj.unit_counit_l_at radjP.
Definition unit_counit_r_at: forall b, unit (F b) \; Fhom F (counit b) ≡ F b := Adj.unit_counit_r_at radjP.
Definition unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _ := Adj.unit_counit_l radjP.
Definition unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _ := Adj.unit_counit_r radjP.

Definition up: forall a b, (adj F a ~> b) -> (a ~> F b) := @Adj.up _ _ _ _ (@radjP _ _ F).
Definition dn: forall a b, (a ~> F b) -> (adj F a ~> b) := @Adj.dn _ _ _ _ (@radjP _ _ F).

Lemma preserve_terminal A: terminal A -> terminal (F A).
Proof. exact:(Adj.preserve_terminal radjP). Defined.

Lemma preserve_Terminal (A: Terminal 𝐂): terminal (F A).
Proof. exact:(preserve_terminal terminalP). Defined.

End binding.
End radj. 

(* TOFIX: wrongly detected forgetful inheritance (two distinct hierarchies) *)
#[export,non_forgetful_inheritance]
HB.instance Definition _ 𝐂 𝐃 F A := IsTerminal.Build _ _ (@radj.preserve_Terminal 𝐂 𝐃 F A).



(** * equivalence [C->D]^op ≃ [C^op->D^op] *)

Section s.
Context {𝐂: PreCat} {𝐃: Cat}.
Definition opfunc (F: ob (Functor 𝐂 𝐃)^op): ob (Functor 𝐂^op 𝐃^op) := funcop F: Functor _ _.
Definition opfunc' (F: ob (Functor 𝐂^op 𝐃^op)): ob (Functor 𝐂 𝐃)^op := funcop' F: Functor _ _.

HB.instance Definition _ :=
  @IsFunctor.Build _ _ opfunc (fun _ _ n => ntxop n: NTX _ _)
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

(* first two instances only need 𝐃: PreCat *)
HB.instance Definition _ :=
  @IsFunctor.Build _ _ opfunc' (fun _ _ n => ntxop' n: NTX _ _)
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ := IsPreAdjointF.Build _ _ opfunc opfunc'.
HB.instance Definition _ := IsPreAdjointF.Build _ _ opfunc' opfunc.

(* TODO: helpers since this is really an identity adjunction, like for [same_functor]? *)
Definition adj_opfunc: adjunction opfunc opfunc'.
  unshelve esplit.
  unshelve esplit.
  cbn=>a. exact: ntx_id.
  split; split. cbn=>F G n a. cat.
  unshelve esplit. 
  unshelve esplit.
  cbn=>a. exact: ntx_id.
  split; split. cbn=>a b f. by rewrite !cats. 
  split; split. cbn=>F G n a. by rewrite !cats.
  cbn=>F a/=. by rewrite !cats. 
  cbn=>F a/=. by rewrite !cats. 
Defined.

Definition adj_opfunc': adjunction opfunc' opfunc.
  unshelve esplit.
  unshelve esplit.
  cbn=>a. exact: ntx_id.
  split; split. cbn=>F G n a. by rewrite !cats. 
  unshelve esplit.
  unshelve esplit.
  cbn=>a. exact: ntx_id.
  split; split. cbn=>a b f. by rewrite !cats. 
  split; split. cbn=>F G n a. cat.
  cbn=>F a/=. by rewrite !cats. 
  cbn=>F a/=. by rewrite !cats. 
Defined.

HB.instance Definition _ := IsLeftAdjoint.Build _ _ opfunc adj_opfunc.
HB.instance Definition _ := IsRightAdjoint.Build _ _ opfunc adj_opfunc'.
HB.instance Definition _ := IsLeftAdjoint.Build _ _ opfunc' adj_opfunc'.
HB.instance Definition _ := IsRightAdjoint.Build _ _ opfunc' adj_opfunc.

End s. 

(** * equivalence C^op^op ≃ C *)

Section s.
Context {𝐂: Cat}.
Definition opop (a: ob 𝐂^op^op): ob 𝐂 := obop' (obop' a).
Definition opop' (a: ob 𝐂): ob 𝐂^op^op := obop (obop a).

HB.instance Definition _ :=
  @IsFunctor.Build _ _ opop (fun _ _ f => morphop' (morphop' f))
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ :=
  @IsFunctor.Build _ _ opop' (fun _ _ f => morphop (morphop f))
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ := IsPreAdjointF.Build _ _ opop opop'.
HB.instance Definition _ := IsPreAdjointF.Build _ _ opop' opop.

(* TODO: helpers since this is really an identity adjunction, like for [same_functor]? *)
Definition adj_opop: adjunction opop opop'.
  unshelve esplit.
  unshelve esplit.
  exact: (fun a => idmap). 
  split; split. cbn=>a b f. by rewrite !cats.
  exact: ntx_id. 
  cbn=>a/=. by rewrite !cats. 
  cbn=>a/=. by rewrite !cats. 
Defined.

Definition adj_opop': adjunction opop' opop.
  unshelve esplit.
  unshelve esplit.
  exact: (fun a => idmap). 
  split; split. cbn=>a b f. by rewrite !cats.
  exact: ntx_id.
  cbn=>a/=. by rewrite !cats. 
  cbn=>a/=. by rewrite !cats. 
Defined.

HB.instance Definition _ := IsLeftAdjoint.Build _ _ opop adj_opop.
HB.instance Definition _ := IsRightAdjoint.Build _ _ opop adj_opop'.
HB.instance Definition _ := IsLeftAdjoint.Build _ _ opop' adj_opop'.
HB.instance Definition _ := IsRightAdjoint.Build _ _ opop' adj_opop.

End s. 
