(** cocones and colimits *)

Require Import cat morphisms functor adjunction limit.
Require Import arewrite.

Open Scope cat_scope.

(** * cocones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃).
  
  Definition cocone := {C & {p: forall c, F c ~> C | forall c c' (f: c' ~> c), Fhom F f \; p c ≡ p c' }}.
  Definition cocone_ob (C: cocone): ob 𝐃 := projT1 C. 
  Definition cocone_mor (C: cocone): forall c, F c ~> cocone_ob C := proj1_sig (projT2 C). 
  Lemma coconeP (C: cocone) c c' (f: c' ~> c): Fhom F f \; cocone_mor C c ≡ cocone_mor C c'.
  Proof. exact: (proj2_sig (projT2 C)). Qed.

  Definition coconehom (C D: cocone) :=
    { h: cocone_ob C ~> cocone_ob D | forall c, cocone_mor C c \; h ≡ cocone_mor D c }.
  Coercion coconehom_sort C D: coconehom C D -> (cocone_ob C ~> cocone_ob D) := @proj1_sig _ _. 
  Lemma coconehomP C D (h: coconehom C D) c: cocone_mor C c \; h ≡ cocone_mor D c.
  Proof. exact: (proj2_sig h). Qed.
  
  HB.instance Definition _ := IsQuiver.Build cocone coconehom.
  
  Definition cocone_id (C: cocone): C ~> C :=
    cone_id (F:=funcop F) C.
  Definition cocone_comp (C D E: cocone) (f: C ~> D) (g: D ~> E): C ~> E :=
    cone_comp (F:=funcop F) g f. 
  HB.instance Definition _ := IsPreCat.Build cocone (@cocone_id) (@cocone_comp).

  (* TODO with a subcategory construction, or by duality *)
  Lemma _cocone_cat: IsCat cocone.
  Proof. 
    split; intros. 
    - exact: comp1o.
    - exact: compo1.
    - exact: compoA.
    - move=>/=f f' ff g g' gg. exact/comp_eqv.
  Qed.  
  HB.instance Definition _ := _cocone_cat. 

  (** * colimits *)
  
  Definition is_colimit := @initial cocone.
  Definition Colimit := Initial cocone.
  
End s.

(** duality between limits and colimits *)
Section s.
Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃).
Definition limit_op C (H: @is_limit _ _ F C): @is_colimit _ _ (funcop F) (obop C) := H. 
Definition colimit_op C (H: @is_colimit _ _ F C): @is_limit _ _ (funcop F) (obop C) := H. 
Definition Limit_op (L: Limit F): Colimit (funcop F) := Terminal_op L. 
Definition Colimit_op (L: Colimit F): Limit (funcop F) := Initial_op L. 
End s.

(** * lifting functors to cocones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃) {𝐄: Cat}.

  Section s.
    Context (G: Functor 𝐃 𝐄).

    Definition Fcocone (x: cocone F): cocone (catcomp F G) :=
      Fcone (F:=funcop F) (funcop G) x.
    
    Definition Fcoconehom (x y: cocone F) (f: coconehom x y): Fcocone x ~> Fcocone y :=
      Fconehom (F:=funcop F) (funcop G) f.
    
    HB.instance Definition _ :=
      @IsFunctor.Build _ _ Fcocone Fcoconehom
        (fun _ _ _ _ H => Fhom_eqv (F:=G) H) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _).
  End s.
  
  (** * lifting (left) adjunctions to cocones *)
  
  Section s.
    Context (G: LeftAdjoint 𝐃 𝐄).

    Definition Fcocone' (x: cocone (catcomp F G)): cocone F :=
      Fcone' (F:=funcop F) (G:=funcop G) x.
    
    Definition Fcocone'hom (x y: cocone (catcomp F G)) (f: coconehom x y): Fcocone' x ~> Fcocone' y.
      move: (Fcone'hom (F:=funcop F) (G:=funcop G) f).
      by cbn.
    Defined.
    
    HB.instance Definition _ :=
      @IsFunctor.Build _ _ Fcocone' Fcocone'hom
        (fun _ _ _ _ H => Fhom_eqv (F:=adj G) H) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _).
    
    HB.instance Definition _ := IsPreAdjointF.Build _ _ (Fcocone G) Fcocone'. 

    Definition Fcocone_adj: adjunction (Fcocone G) Fcocone' :=
      (* TOFIX: LOOONG *)
      Adj.op (Fcone_adj (funcop F) (funcop G)). 
    HB.instance Definition _ := IsLeftAdjoint.Build _ _ (Fcocone G) Fcocone_adj.

    (** * left adjoints preserve colimits *)
    Theorem ladj_preserve_colimit (A: cocone F): is_colimit A -> is_colimit (Fcocone G A).
    Proof. exact/ladj.preserve_initial. Defined.

    HB.instance Definition _ (A: Colimit F) :=
      IsInitial.Build _ (Fcocone G (INITIAL.sort A)) (ladj_preserve_colimit initialP). 
  End s.
  
End s.


(** * equivalent diagrams yield equivalent categories of cocones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat}.
  Definition transport_cocone (F G: Diagram 𝐂 𝐃) (n: G ~> F) (C: cocone F): cocone G.
  Proof. exact: (transport_cone (ntxop n: NTX _ _)). Defined.
  Definition transport_coconehom (F G: Diagram 𝐂 𝐃) (n: G ~> F) (C D: cocone F) (h: coconehom C D):
    coconehom (transport_cocone n C) (transport_cocone n D).
  Proof. exact: (transport_conehom (ntxop n: NTX _ _)). Defined.

  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: G ~> F) :=
    @IsFunctor.Build _ _ (transport_cocone n) (transport_coconehom n)
      (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: G ≃ F) :=
    IsPreAdjointF.Build _ _ (transport_cocone n) (transport_cocone n⁻¹). 

  Definition transport_cocone_ladj (F G: Diagram 𝐂 𝐃) (n: G ≃ F):
    adjunction (transport_cocone n) (transport_cocone n⁻¹).
  Proof.
    set n' := @iso_ (Diagram _ _) _ _ (ntxop n⁻¹: NTX _ _) (ntxop n¹: NTX _ _) (isoP n).
    (* TOFIX: LOOOONG *)
    exact: (Adj.op (@transport_cone_ladj _ _ (funcop G) (funcop F) n')).
  Defined.
  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: G ≃ F) :=
    IsLeftAdjoint.Build _ _ (transport_cocone n) (transport_cocone_ladj n). 
  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: G ≃ F) :=
    IsRightAdjoint.Build _ _ (transport_cocone n) (transport_cocone_ladj n⁻¹). 
  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: G ≃ F) :=
    IsAdjointEquivalence.Build _ _ (transport_cocone n). 
End s.


(** * creating colimits through left reflections *)

Definition colimits (S: BareQuiver) (𝐂: Cat) := forall D: Diagram S 𝐂, Colimit D.

Section s.  
  Context {𝐂 𝐃: Cat} (F: LeftReflection 𝐂 𝐃) (S: BareQuiver).
  Hypothesis colim: colimits S 𝐂.
  Theorem lrefl_create_colimits: colimits S 𝐃.
  Proof.
    set lim𝐂op := fun D: Diagram S^op 𝐂^op => Colimit_op (colim (funcop' D)).
    set lim𝐃op := rcorefl_create_limits (funcop F) lim𝐂op.
    exact: (fun D => Limit_op (lim𝐃op (funcop D))).
  Defined.
End s.


(** * HB packaging *)


(** ** categories with all colimits of shape [S] *)
#[primitive] HB.mixin Record HasColimits (S: BareQuiver) 𝐂 & CAT 𝐂 := 
  { #[canonical=no] colim: colimits S 𝐂 }.

#[short(type="CatColim")]
HB.structure Definition CATCOLIM (S: BareQuiver) := { 𝐂 of HasColimits S 𝐂 & }.
Definition mk_colimits S 𝐂 (colim: colimits S 𝐂): Type := 𝐂.
Arguments mk_colimits _ {_} _/.
HB.instance Definition _ S 𝐂 colim := CAT.on (@mk_colimits S 𝐂 colim).
HB.instance Definition _ S 𝐂 colim := @HasColimits.Build S (@mk_colimits S 𝐂 colim) colim.

HB.factory Record HasColimitsThroughAdj S (𝐃: CatColim S) 𝐂 & CAT 𝐂 := { F: LeftReflection 𝐃 𝐂 }.
HB.builders Context S 𝐃 𝐂 & HasColimitsThroughAdj S 𝐃 𝐂.
HB.instance Definition _ := HasColimits.Build S 𝐂 (lrefl_create_colimits F colim).
HB.end.
