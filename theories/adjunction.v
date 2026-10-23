(** * adjunctions *)

Require Import cat morphisms functor.
Require Import arewrite.

Open Scope cat_scope.

(** ** adjunctions *)

Module Adj.
  Section def.
  Context (𝐂 𝐃: PreCat) (F: PreFunctor 𝐂 𝐃) (G: PreFunctor 𝐃 𝐂).
  Record adjunction :=
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
  Definition is_reflection s := sig (is_iso_tx (counit s)).
  Definition counit' s (x: is_reflection s): TX idfun (catcomp G F) := sval x.
  Definition is_coreflection s := sig (is_iso_tx (unit s)).
  Definition unit' s (x: is_coreflection s): TX (catcomp F G) idfun := sval x.
  End def.
  Infix "⊣" := adjunction (at level 79): cat_scope.
  Arguments adjunction: clear implicits.
  Arguments mk {_ _ _ _} &.
  
  Section theory.
  Context {𝐂 𝐃: Cat} {F G: Functor _ _} (s: adjunction 𝐂 𝐃 F G).
  
  Definition unit_: functor_id ~> functor_comp F G := unit s. (* abbreviation? *)
  Definition counit_: functor_comp G F ~> functor_id := counit s. (* abbreviation? *)
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

  Lemma refl_corefl_equiv:
    is_reflection s -> is_coreflection s -> G ⊣ F. 
  Proof.
    move=>R C.
    unshelve apply: mk.
    - unshelve eexists. exact: (counit' R). sorry.
    - unshelve eexists. exact: (unit' C). sorry.
    - sorry.
    - sorry.
  Defined.

  Lemma refl_corefl_equiv_refl
    (R: is_reflection s) (C: is_coreflection s):
    is_reflection (refl_corefl_equiv R C).
  Proof. exists (unit s). exact/iso_txC /(proj2_sig C). Defined.

  Lemma refl_corefl_equiv_corefl
    (R: is_reflection s) (C: is_coreflection s):
    is_coreflection (refl_corefl_equiv R C).
  Proof. exists (counit s). exact/iso_txC /(proj2_sig R). Defined.

  Lemma equiv_refl (s': G ⊣ F): is_reflection s.
  Proof.
    exists (unit s')=>a. sorry. 
  Defined.      

  Lemma equiv_corefl (s': G ⊣ F): is_coreflection s.
  Proof.
    exists (counit s'). sorry. 
  Defined.      
  
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
      (unit_ FF \; idmap ⊚ unit_ GG ⊚ idmap)
      (idmap ⊚ counit_ FF ⊚ idmap \; counit_ GG) _ _.
  Next Obligation. move=>𝐂 𝐃 𝐄 F F' G G' FF GG A/=. sorry. Qed.
  Next Obligation. move=>𝐂 𝐃 𝐄 F F' G G' FF GG B/=. sorry. Qed.

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

  Definition refl_op {𝐂 𝐃 F G} (FG: adjunction 𝐂 𝐃 F G) (H: is_reflection FG):
    is_coreflection (op FG).
    exists (counit' H). exact/iso_txC/(proj2_sig H).
  Defined.

  Definition corefl_op {𝐂 𝐃 F G} (FG: adjunction 𝐂 𝐃 F G) (H: is_coreflection FG):
    is_reflection (op FG).
    exists (unit' H). exact/iso_txC/(proj2_sig H).
  Defined.

  Definition refl_op' {𝐂 𝐃 F G} (FG: F ⊣ G) (H: is_reflection FG):
    @is_coreflection 𝐃 𝐂 _ _ (op' FG) := refl_op H.

  Definition corefl_op' {𝐂 𝐃 F G} (FG: F ⊣ G) (H: is_coreflection FG):
    @is_reflection 𝐃 𝐂 _ _ (op' FG) := corefl_op H.
  
End Adj.
Definition adjunction := Adj.adjunction.
Infix "⊣" := adjunction (at level 79): cat_scope.

(** * HB inference *)

(** ** functions with an adjoint candidate (either left or right, or both) *)

#[primitive] 
HB.mixin Record IsPreAdjoint {𝐂 𝐃} (F: FUN 𝐂 𝐃) :=
  { #[canonical=no] adj: FUN 𝐃 𝐂 }.
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
HB.mixin Record IsLeftAdjoint 𝐂 𝐃 F of @PREADJOINTF 𝐂 𝐃 F :=
  { #[canonical=no] ladjP: F ⊣ adj F; }.
#[short(type="LeftAdjoint")]
HB.structure Definition LEFTADJOINT 𝐂 𝐃 := {F of IsLeftAdjoint 𝐂 𝐃 F & }.

#[primitive] 
HB.mixin Record IsRightAdjoint 𝐂 𝐃 F of @PREADJOINTF 𝐂 𝐃 F :=
  { #[canonical=no] radjP: adj F ⊣  F }.
#[short(type="RightAdjoint")]
HB.structure Definition RIGHTADJOINT 𝐂 𝐃 := {F of IsRightAdjoint 𝐂 𝐃 F & }.

(** ** functors taking part into a reflection *)

#[primitive] 
HB.mixin Record IsLeftReflection 𝐂 𝐃 F of @LEFTADJOINT 𝐂 𝐃 F :=
  { #[canonical=no] lreflP: Adj.is_reflection (ladjP (s:=F)); }.
#[short(type="LeftReflection")]
HB.structure Definition LEFTREFLECTION 𝐂 𝐃 := {F of IsLeftReflection 𝐂 𝐃 F & }.

#[primitive] 
HB.mixin Record IsRightReflection 𝐂 𝐃 F of @RIGHTADJOINT 𝐂 𝐃 F :=
  { #[canonical=no] rreflP: Adj.is_reflection (radjP (s:=F)); }.
#[short(type="RightReflection")]
HB.structure Definition RIGHTREFLECTION 𝐂 𝐃 := {F of IsRightReflection 𝐂 𝐃 F & }.

(** ** functors taking part into a coreflection *)

#[primitive] 
HB.mixin Record IsLeftCoreflection 𝐂 𝐃 F of @LEFTADJOINT 𝐂 𝐃 F :=
  { #[canonical=no] lcoreflP: Adj.is_coreflection (ladjP (s:=F)); }.
#[short(type="LeftCoreflection")]
HB.structure Definition LEFTCOREFLECTION 𝐂 𝐃 := {F of IsLeftCoreflection 𝐂 𝐃 F & }.

#[primitive] 
HB.mixin Record IsRightCoreflection 𝐂 𝐃 F of @RIGHTADJOINT 𝐂 𝐃 F :=
  { #[canonical=no] rcoreflP: Adj.is_coreflection (radjP (s:=F)); }.
#[short(type="RightCoreflection")]
HB.structure Definition RIGHTCOREFLECTION 𝐂 𝐃 := {F of IsRightCoreflection 𝐂 𝐃 F & }.

(** ** adjoint equivalences *)

(* we use an empty mixin because HB does seem to be able to saturate instances appropriately *)
HB.mixin Record IsAdjointEquivalence_ 𝐂 𝐃 F of
  @LEFTREFLECTION 𝐂 𝐃 F &
  @LEFTCOREFLECTION 𝐂 𝐃 F &
  @RIGHTREFLECTION 𝐂 𝐃 F &
  @RIGHTCOREFLECTION 𝐂 𝐃 F := {}.

#[short(type="AdjointEquivalence")]
  HB.structure Definition ADJOINTEQUIVALENCE 𝐂 𝐃 :=
  {F of IsAdjointEquivalence_ 𝐂 𝐃 F & }.

(** being both a left and right adjoint (for the same adjoint candidate) is enough *)
HB.factory Record IsAdjointEquivalence (𝐂 𝐃: Cat) F of @LEFTADJOINT 𝐂 𝐃 F & @RIGHTADJOINT 𝐂 𝐃 F := {}.
HB.builders Context 𝐂 𝐃 F of IsAdjointEquivalence 𝐂 𝐃 F.
HB.instance Definition _ :=
  IsLeftReflection.Build _ _ F (Adj.equiv_refl ladjP (radjP (s:=F))).
HB.instance Definition _ :=
  IsLeftCoreflection.Build _ _ F (Adj.equiv_corefl ladjP (radjP (s:=F))).
HB.instance Definition _ :=
  IsRightReflection.Build _ _ F (Adj.equiv_refl radjP (ladjP (s:=F))).
HB.instance Definition _ :=
  IsRightCoreflection.Build _ _ F (Adj.equiv_corefl radjP (ladjP (s:=F))).
HB.instance Definition _ :=
  IsAdjointEquivalence_.Build _ _ F.
HB.end.

(** being both a left reflection and a right reflection is enough *)
HB.factory Record IsAdjointEquivalenceL (𝐂 𝐃: Cat) F of @LEFTREFLECTION 𝐂 𝐃 F & @LEFTCOREFLECTION 𝐂 𝐃 F := {}.
HB.builders Context 𝐂 𝐃 F of IsAdjointEquivalenceL 𝐂 𝐃 F.
HB.instance Definition _ :=
  IsRightAdjoint.Build _ _ F (Adj.refl_corefl_equiv (lreflP (s:=F)) (lcoreflP (s:=F))).
HB.instance Definition _ :=
  IsRightReflection.Build _ _ F (Adj.refl_corefl_equiv_refl _ _).
HB.instance Definition _ :=
  IsRightCoreflection.Build _ _ F (Adj.refl_corefl_equiv_corefl _ _).
HB.instance Definition _ :=
  IsAdjointEquivalence_.Build _ _ F.
HB.end.


(** * adjunction instances *)

(** ** duality instances *)

(* LA <-adj-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: LeftAdjoint 𝐂 𝐃) :=
  IsRightAdjoint.Build 𝐃 𝐂 (adj F) ladjP.
HB.instance Definition _ 𝐂 𝐃 (F: RightAdjoint 𝐂 𝐃) :=
  IsLeftAdjoint.Build 𝐃 𝐂 (adj F) radjP.

HB.instance Definition _ 𝐂 𝐃 (F: LeftReflection 𝐂 𝐃) :=
  IsRightReflection.Build 𝐃 𝐂 (adj F) lreflP.
HB.instance Definition _ 𝐂 𝐃 (F: RightReflection 𝐂 𝐃) :=
  IsLeftReflection.Build 𝐃 𝐂 (adj F) rreflP.

HB.instance Definition _ 𝐂 𝐃 (F: LeftCoreflection 𝐂 𝐃) :=
  IsRightCoreflection.Build 𝐃 𝐂 (adj F) lcoreflP.
HB.instance Definition _ 𝐂 𝐃 (F: RightCoreflection 𝐂 𝐃) :=
  IsLeftCoreflection.Build 𝐃 𝐂 (adj F) rcoreflP.

HB.instance Definition _ 𝐂 𝐃 (F: AdjointEquivalence 𝐂 𝐃) :=
  IsAdjointEquivalence_.Build _ _ (adj F).

(* LA <-funcop-> RA *)
HB.instance Definition _ 𝐂 𝐃 (F: LeftAdjoint 𝐂 𝐃) :=
  IsRightAdjoint.Build _ _ (funcop F) (Adj.op ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: RightAdjoint 𝐂 𝐃) :=
  IsLeftAdjoint.Build _ _ (funcop F) (Adj.op radjP).
HB.instance Definition _ 𝐂 𝐃 (F: LeftAdjoint _ _) :=
  IsRightAdjoint.Build 𝐂 𝐃 (funcop' F) (Adj.op' ladjP).
HB.instance Definition _ 𝐂 𝐃 (F: RightAdjoint _ _) :=
  IsLeftAdjoint.Build 𝐂 𝐃 (funcop' F) (Adj.op' radjP).

HB.instance Definition _ 𝐂 𝐃 (F: LeftReflection 𝐂 𝐃) :=
  IsRightCoreflection.Build _ _ (funcop F) (Adj.refl_op lreflP).
HB.instance Definition _ 𝐂 𝐃 (F: RightReflection 𝐂 𝐃) :=
  IsLeftCoreflection.Build _ _ (funcop F) (Adj.refl_op rreflP).
HB.instance Definition _ 𝐂 𝐃 (F: LeftReflection _ _) :=
  IsRightCoreflection.Build 𝐂 𝐃 (funcop' F) (Adj.refl_op' lreflP).
HB.instance Definition _ 𝐂 𝐃 (F: RightReflection _ _) :=
  IsLeftCoreflection.Build 𝐂 𝐃 (funcop' F) (Adj.refl_op' rreflP).

HB.instance Definition _ 𝐂 𝐃 (F: LeftCoreflection 𝐂 𝐃) :=
  IsRightReflection.Build _ _ (funcop F) (Adj.corefl_op lcoreflP).
HB.instance Definition _ 𝐂 𝐃 (F: RightCoreflection 𝐂 𝐃) :=
  IsLeftReflection.Build _ _ (funcop F) (Adj.corefl_op rcoreflP).
HB.instance Definition _ 𝐂 𝐃 (F: LeftCoreflection _ _) :=
  IsRightReflection.Build 𝐂 𝐃 (funcop' F) (Adj.corefl_op' lcoreflP).
HB.instance Definition _ 𝐂 𝐃 (F: RightCoreflection _ _) :=
  IsLeftReflection.Build 𝐂 𝐃 (funcop' F) (Adj.corefl_op' rcoreflP).

HB.instance Definition _ 𝐂 𝐃 (F: AdjointEquivalence 𝐂 𝐃) :=
  IsAdjointEquivalence_.Build _ _ (funcop F).
HB.instance Definition _ 𝐂 𝐃 (F: AdjointEquivalence _ _) :=
  IsAdjointEquivalence_.Build 𝐂 𝐃 (funcop' F).

(* TODO: funcop12 *)

(** ** identity adjunctions *)
HB.instance Definition _ (𝐂: Cat) := IsLeftAdjoint.Build 𝐂 𝐂 idfun Adj.id.
HB.instance Definition _ (𝐂: Cat) := IsRightAdjoint.Build 𝐂 𝐂 idfun Adj.id.
HB.instance Definition _ (𝐂: Cat) := IsAdjointEquivalence.Build 𝐂 𝐂 idfun.

(** ** composing adjunctions  *)
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: LeftAdjoint 𝐂 𝐃) (G: LeftAdjoint 𝐃 𝐄) :=
  IsLeftAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp ladjP ladjP).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: RightAdjoint 𝐂 𝐃) (G: RightAdjoint 𝐃 𝐄) :=
  IsRightAdjoint.Build 𝐂 𝐄 (catcomp F G) (Adj.comp radjP radjP).
HB.instance Definition _ (𝐂 𝐃 𝐄: Cat) (F: AdjointEquivalence 𝐂 𝐃) (G: AdjointEquivalence 𝐃 𝐄) :=
  IsAdjointEquivalence.Build 𝐂 𝐄 (catcomp F G).

Check fun (C D: Cat) (F: AdjointEquivalence C D) => adj F: AdjointEquivalence D C. 
Check fun (C D: Cat) (F: AdjointEquivalence C D) => funcop F: AdjointEquivalence (C^op) (D^op). 
Check fun (C: Cat) (F G: AdjointEquivalence C C) => catcomp F G: AdjointEquivalence C C. 


(** * binding properties of adjunctions to HB's inferrence *)

Module ladj.
Section binding.
Context {𝐂 𝐃: Cat} (F: LeftAdjoint 𝐂 𝐃).

Definition unit: functor_id ~> functor_comp F (adj F) := Adj.unit ladjP.
Definition counit: functor_comp (adj F) F ~> functor_id := Adj.counit ladjP.
Definition unit_counit_l_at: forall a, Fhom F (unit a) \; counit (F a) ≡ F a := Adj.unit_counit_l_at ladjP.
Definition unit_counit_r_at: forall b, unit (adj F b) \; Fhom (adj F) (counit b) ≡ adj F b := Adj.unit_counit_r_at ladjP.
Definition unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _ := Adj.unit_counit_l ladjP.
Definition unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _ := Adj.unit_counit_r ladjP.

Definition up: forall a b, (F a ~> b) -> (a ~> adj F b) := @Adj.up _ _ _ _ (@ladjP _ _ F).
Definition dn: forall a b, (a ~> adj F b) -> (F a ~> b) := @Adj.dn _ _ _ _ (@ladjP _ _ F).

Lemma preserve_initial A: initial A -> initial (F A).
Proof. exact:(Adj.preserve_initial ladjP). Defined.

Definition preserve_Initial (A: Initial 𝐂): Initial 𝐃 :=
  mk_initial (F A) (preserve_initial initialP). 

End binding.
End ladj.

Module radj.
Section binding.
Context {𝐂 𝐃: Cat} (F: RightAdjoint 𝐂 𝐃).

Definition unit: functor_id ~> functor_comp (adj F) F := Adj.unit radjP.
Definition counit: functor_comp F (adj F) ~> functor_id := Adj.counit radjP.
Definition unit_counit_l_at: forall a, Fhom (adj F) (unit a) \; counit (adj F a) ≡ adj F a := Adj.unit_counit_l_at radjP.
Definition unit_counit_r_at: forall b, unit (F b) \; Fhom F (counit b) ≡ F b := Adj.unit_counit_r_at radjP.
Definition unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _ := Adj.unit_counit_l radjP.
Definition unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _ := Adj.unit_counit_r radjP.

Definition up: forall a b, (adj F a ~> b) -> (a ~> F b) := @Adj.up _ _ _ _ (@radjP _ _ F).
Definition dn: forall a b, (a ~> F b) -> (adj F a ~> b) := @Adj.dn _ _ _ _ (@radjP _ _ F).

Lemma preserve_terminal A: terminal A -> terminal (F A).
Proof. exact:(Adj.preserve_terminal radjP). Defined.

Definition preserve_Terminal (A: Terminal 𝐂): Terminal 𝐃 :=
  mk_terminal (F A) (preserve_terminal terminalP). 

End binding.
End radj. 

Module lrefl.
Section binding.
Context {𝐂 𝐃: Cat} (F: LeftReflection 𝐂 𝐃).
Definition counit': TX idfun (catcomp (adj F) F) := Adj.counit' lreflP.
Definition iso_tx_counit: is_iso_tx (ladj.counit F) counit' := proj2_sig lreflP. 
Definition counit: functor_comp (adj F) F ≃ functor_id.
  exact/iso_functor/(iso_ntx' iso_tx_counit).
Defined.
End binding.
End lrefl.
HB.instance Definition _ {𝐂 𝐃: Cat} (F: LeftReflection 𝐂 𝐃) :=
  ISO.copy (ladj.counit F) (lrefl.counit F).

Module lcorefl.
Section binding.
Context {𝐂 𝐃: Cat} (F: LeftCoreflection 𝐂 𝐃).
Definition unit': TX (catcomp F (adj F)) idfun := Adj.unit' lcoreflP.
Definition iso_tx_unit: is_iso_tx (ladj.unit F) unit' := proj2_sig lcoreflP. 
Definition unit: functor_id ≃ functor_comp F (adj F).
  exact/iso_functor/(iso_ntx' iso_tx_unit).
Defined.
End binding.
End lcorefl.
HB.instance Definition _ {𝐂 𝐃: Cat} (F: LeftCoreflection 𝐂 𝐃) :=
  ISO.copy (ladj.unit F) (lcorefl.unit F).

Module rrefl.
Section binding.
Context {𝐂 𝐃: Cat} (F: RightReflection 𝐂 𝐃).
Definition counit': TX idfun (catcomp F (adj F)) := Adj.counit' rreflP.
Definition iso_tx_counit: is_iso_tx (radj.counit F) counit' := proj2_sig rreflP. 
Definition counit: functor_comp F (adj F) ≃ functor_id.
  exact/iso_functor/(iso_ntx' iso_tx_counit).
Defined.
End binding.
End rrefl.
HB.instance Definition _ {𝐂 𝐃: Cat} (F: RightReflection 𝐂 𝐃) :=
  ISO.copy (radj.counit F) (rrefl.counit F).

Module rcorefl.
Section binding.
Context {𝐂 𝐃: Cat} (F: RightCoreflection 𝐂 𝐃).
Definition unit': TX (catcomp (adj F) F) idfun := Adj.unit' rcoreflP.
Definition iso_tx_unit: is_iso_tx (radj.unit F) unit' := proj2_sig rcoreflP. 
Definition unit: functor_id ≃ functor_comp (adj F) F.
  exact/iso_functor/(iso_ntx' iso_tx_unit).
Defined.
End binding.
End rcorefl.
HB.instance Definition _ {𝐂 𝐃: Cat} (F: RightCoreflection 𝐂 𝐃) :=
  ISO.copy (radj.unit F) (rcorefl.unit F).


(** * equivalence C^op^op ≃ C *)

Section s.
Context {𝐂: Cat}.
Definition opop: FUN 𝐂^op^op 𝐂 := fun a => obop' (obop' a).
Definition opop': FUN 𝐂 𝐂^op^op := fun a => obop (obop a).

HB.instance Definition _ :=
  @IsFunctor.Build _ _ opop (fun _ _ f => morphop' (morphop' f))
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ :=
  @IsFunctor.Build _ _ opop' (fun _ _ f => morphop (morphop f))
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ := IsPreAdjointF.Build _ _ opop opop'.

(* TODO: helpers since this is really an identity adjunction, like for [same_functor]? *)
Definition adj_opop: adjunction opop opop'.
Proof.
  unshelve esplit.
  unshelve esplit.
  exact: (fun a => idmap). 
  split; split. cbn=>a b f. by rewrite !cats.
  exact: ntx_id. 
  cbn=>a/=. by rewrite !cats. 
  cbn=>a/=. by rewrite !cats. 
Defined.

HB.instance Definition _ := IsLeftAdjoint.Build _ _ opop adj_opop.
HB.instance Definition _ := IsLeftReflection.Build _ _ opop (iso_tx_id' _).
HB.instance Definition _ := IsLeftCoreflection.Build _ _ opop (iso_tx_id' _).
HB.instance Definition _ := IsAdjointEquivalenceL.Build _ _ opop.
HB.instance Definition _ := ADJOINTEQUIVALENCE.copy opop' (adj opop).

End s. 


(** * equivalence [C->D]^op ≃ [C^op->D^op] *)

Section s.
Context {𝐂: PreCat} {𝐃: Cat}.
Definition opfunc: FUN (Functor 𝐂 𝐃)^op (Functor 𝐂^op 𝐃^op) := fun F => funcop F: Functor _ _.
Definition opfunc': FUN (Functor 𝐂^op 𝐃^op) (Functor 𝐂 𝐃)^op := fun F => funcop' F: Functor _ _.

HB.instance Definition _ :=
  @IsFunctor.Build _ _ opfunc (fun _ _ n => ntxop n: NTX _ _)
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ :=
  @IsFunctor.Build _ _ opfunc' (fun _ _ n => ntxop' n: NTX _ _)
    (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

HB.instance Definition _ := IsPreAdjointF.Build _ _ opfunc opfunc'.

(* TODO: helpers since this is really an identity adjunction, like for [same_functor]? *)
Definition adj_opfunc: adjunction opfunc opfunc'.
Proof.
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

Definition refl_adj_opfunc: Adj.is_reflection adj_opfunc.
Proof.
  unshelve eexists.
  cbn=>a. exact: idmap.
  move=>F. split; cbn=>a; by rewrite !cats.
Defined.

Definition corefl_adj_opfunc: Adj.is_coreflection adj_opfunc.
Proof.
  unshelve eexists.
  cbn=>a. exact: idmap.
  move=>F. split; cbn=>a; by rewrite !cats.
Defined.

HB.instance Definition _ := IsLeftAdjoint.Build _ _ opfunc adj_opfunc.
HB.instance Definition _ := IsLeftReflection.Build _ _ opfunc refl_adj_opfunc.
HB.instance Definition _ := IsLeftCoreflection.Build _ _ opfunc corefl_adj_opfunc.
HB.instance Definition _ := IsAdjointEquivalenceL.Build _ _ opfunc.
HB.instance Definition _ := ADJOINTEQUIVALENCE.copy opfunc' (adj opfunc).

End s. 


(** * adjunction C D -> adjunction [D->E] ≃ [C->E]
      (reversing polarities) *)

Definition Fprecomp {𝐂 𝐃: Cat} (F: Functor 𝐂 𝐃) (𝐄: Cat): FUN (Functor 𝐃 𝐄) (Functor 𝐂 𝐄) :=
  fun H => catcomp F H: Functor _ _.
Arguments Fprecomp {_ _} _ {_}.

(* TOFIX: super long if [ntx_comp'_eqv] is declared as an instance in [adjunction.v] *)
Program Definition _Fprecomp_functor 𝐂 𝐃 F 𝐄 :=
  @IsFunctor.Build _ _ (@Fprecomp 𝐂 𝐃 F 𝐄) (fun _ _ n => n ⊚ idmap) _ _ _.
Next Obligation. move=>*n m nm. exact/ntx_comp'_eqv. Qed.
Next Obligation. move=>*. exact/ntx_comp'_id. Qed.
Next Obligation.
  move=>*/=. rewrite -ntx_comp'_comp (* cats *).
  etransitivity. apply: ntx_comp'_eqv. 2,3: done. cat.
Qed.
HB.instance Definition _ 𝐂 𝐃 F 𝐄 := @_Fprecomp_functor 𝐂 𝐃 F 𝐄.

HB.instance Definition _ (𝐂 𝐃: Cat) (F: PreAdjointF 𝐂 𝐃) (𝐄: Cat) :=
  IsPreAdjointF.Build (Functor 𝐃 𝐄) (Functor 𝐂 𝐄) (Fprecomp F) (Fprecomp (adj F)).

Lemma Fprecomp_ladj (𝐂 𝐃: Cat) (F: RightAdjoint 𝐂 𝐃) (𝐄: Cat):
  @adjunction (Functor 𝐃 𝐄) (Functor 𝐂 𝐄) (Fprecomp F) (Fprecomp (adj F)).
Proof.
  unshelve esplit.
  - unshelve esplit.
    move=>H. exact: (ntx_comp' (radj.unit F) (ntx_id H)).
    sorry.
  - unshelve esplit.
    move=>H. exact: (ntx_comp' (radj.counit F) (ntx_id H)).
    sorry.
  - cbn; intros. sorry.
  - cbn; intros. sorry.
Defined.

HB.instance Definition _ (𝐂 𝐃: Cat) (F: RightAdjoint 𝐂 𝐃) (𝐄: Cat) :=
  IsLeftAdjoint.Build (Functor 𝐃 𝐄) (Functor 𝐂 𝐄) (Fprecomp F) (Fprecomp_ladj F 𝐄).
HB.instance Definition _ (𝐂 𝐃: Cat) (F: LeftAdjoint 𝐂 𝐃) (𝐄: Cat) :=
  IsRightAdjoint.Build (Functor 𝐃 𝐄) (Functor 𝐂 𝐄) (Fprecomp F) (Fprecomp_ladj (adj F) 𝐄).
HB.instance Definition _ (𝐂 𝐃: Cat) (F: AdjointEquivalence 𝐂 𝐃) (𝐄: Cat) :=
  IsAdjointEquivalence.Build (Functor 𝐃 𝐄) (Functor 𝐂 𝐄) (Fprecomp F).

(** * adjunction C D -> adjunction [E->C] ≃ [E->D]
      (preserving polarities) *)

Definition Fpostcomp {𝐂 𝐃: Cat} (F: Functor 𝐂 𝐃) (𝐄: Cat): FUN (Functor 𝐄 𝐂) (Functor 𝐄 𝐃) :=
  fun H => catcomp H F: Functor _ _.
Arguments Fpostcomp {_ _} _ {_}.

Program Definition _Fpostcomp_functor 𝐂 𝐃 F 𝐄 :=
  @IsFunctor.Build _ _ (@Fpostcomp 𝐂 𝐃 F 𝐄) (fun _ _ n => idmap ⊚ n) _ _ _.
Next Obligation. move=>*n m nm. exact/ntx_comp'_eqv. Qed.
Next Obligation. move=>*. exact/ntx_comp'_id. Qed.
Next Obligation.
  move=>*/=. rewrite -ntx_comp'_comp (* cats *).
  etransitivity. apply: ntx_comp'_eqv. 1,3: done. cat.
Qed.
HB.instance Definition _ 𝐂 𝐃 F 𝐄 := @_Fpostcomp_functor 𝐂 𝐃 F 𝐄.

HB.instance Definition _ (𝐂 𝐃: Cat) (F: PreAdjointF 𝐂 𝐃) (𝐄: Cat) :=
  IsPreAdjointF.Build (Functor 𝐄 𝐂) (Functor 𝐄 𝐃) (Fpostcomp F) (Fpostcomp (adj F)).

Lemma Fpostcomp_ladj (𝐂 𝐃: Cat) (F: LeftAdjoint 𝐂 𝐃) (𝐄: Cat):
  @adjunction (Functor 𝐄 𝐂) (Functor 𝐄 𝐃) (Fpostcomp F) (Fpostcomp (adj F)).
Proof.
  unshelve esplit.
  - unshelve esplit.
    move=>H. exact: (ntx_comp' (ntx_id H) (ladj.unit F)).
    sorry.
  - unshelve esplit.
    move=>H. exact: (ntx_comp' (ntx_id H) (ladj.counit F)).
    sorry.
  - cbn; intros. sorry.
  - cbn; intros. sorry.
Defined.

HB.instance Definition _ (𝐂 𝐃: Cat) (F: LeftAdjoint 𝐂 𝐃) (𝐄: Cat) :=
  IsLeftAdjoint.Build (Functor 𝐄 𝐂) (Functor 𝐄 𝐃) (Fpostcomp F) (Fpostcomp_ladj F 𝐄).
HB.instance Definition _ (𝐂 𝐃: Cat) (F: RightAdjoint 𝐂 𝐃) (𝐄: Cat) :=
  IsRightAdjoint.Build (Functor 𝐄 𝐂) (Functor 𝐄 𝐃) (Fpostcomp F) (Fpostcomp_ladj (adj F) 𝐄).
HB.instance Definition _ (𝐂 𝐃: Cat) (F: AdjointEquivalence 𝐂 𝐃) (𝐄: Cat) :=
  IsAdjointEquivalence.Build (Functor 𝐄 𝐂) (Functor 𝐄 𝐃) (Fpostcomp F).

(** * adjunction C' C -> adjunction D D' -> adjunction [C->D] ≃ [C'->D']
      (with appropriate polarities) *)

Section s.
Context {𝐂' 𝐂 𝐃 𝐃': Cat}.
Definition Functor_adj (F: Functor 𝐂' 𝐂) (G: Functor 𝐃 𝐃'): FUN (Functor 𝐂 𝐃) (Functor 𝐂' 𝐃') :=
  catcomp (Fprecomp F) (Fpostcomp G).

HB.instance Definition _ (F: Functor 𝐂' 𝐂) (G: Functor 𝐃 𝐃') :=
  FUNCTOR.on (Functor_adj F G).
HB.instance Definition _ (F: PreAdjointF 𝐂' 𝐂) (G: PreAdjointF 𝐃 𝐃') :=
  PREADJOINTF.on (Functor_adj F G).
HB.instance Definition _ (F: RightAdjoint 𝐂' 𝐂) (G: LeftAdjoint 𝐃 𝐃') :=
  LEFTADJOINT.on (Functor_adj F G).
HB.instance Definition _ (F: LeftAdjoint 𝐂' 𝐂) (G: RightAdjoint 𝐃 𝐃') :=
  RIGHTADJOINT.on (Functor_adj F G).
(* TOFIX: HB lags *)
HB.instance Definition _ (F: AdjointEquivalence 𝐂' 𝐂) (G: AdjointEquivalence 𝐃 𝐃') :=
  ADJOINTEQUIVALENCE.on (Functor_adj F G).
End s. 

(** * equivalence [C^op->D^op]^op ≃ [C->D] ≃  as a corollary*)

Section s.
Context {𝐂 𝐃: Cat}.
Definition deopfunc: FUN (Functor 𝐂^op 𝐃^op)^op (Functor 𝐂 𝐃) :=
  catcomp opfunc (Functor_adj opop' opop).
HB.instance Definition _ := ADJOINTEQUIVALENCE.on deopfunc.
End s.
