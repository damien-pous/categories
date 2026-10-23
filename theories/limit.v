(** cones and limits *)

Require Import cat morphisms functor adjunction.
Require Import arewrite.

Open Scope cat_scope.

(** * cones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃).
  
  (* TOIMPROVE: use natural transformations *)
  Definition cone := {C & {p: forall c, C ~> F c | forall c c' (f: c ~> c'), p c \; Fhom F f ≡ p c' }}.
  Definition cone_ob (C: cone): ob 𝐃 := projT1 C. 
  Definition cone_mor (C: cone): forall c, cone_ob C ~> F c := proj1_sig (projT2 C). 
  Lemma coneP (C: cone) c c' (f: c ~> c'): cone_mor C c \; Fhom F f ≡ cone_mor C c'.
  Proof. exact: (proj2_sig (projT2 C)). Qed.

  Definition conehom (C D: cone) :=
    { h: cone_ob C ~> cone_ob D | forall c, h \; cone_mor D c ≡ cone_mor C c }.
  Coercion conehom_sort C D: conehom C D -> (cone_ob C ~> cone_ob D) := @proj1_sig _ _. 
  Lemma conehomP C D (h: conehom C D) c: h \; cone_mor D c ≡ cone_mor C c.
  Proof. exact: (proj2_sig h). Qed.
  
  HB.instance Definition _ := IsQuiver.Build cone conehom.

  Program Definition cone_id (C: cone): C ~> C := exist _ idmap _.
  Next Obligation. move=>/=C c. cat. Qed.
  Program Definition cone_comp (C D E: cone) (f: C ~> D) (g: D ~> E): C ~> E :=
    exist _ (f \; g) _.
  Next Obligation.
    move=>C D E f g c. arewrite conehomP. exact/conehomP.
  Qed.
  HB.instance Definition _ := IsPreCat.Build cone (@cone_id) (@cone_comp).

  (* TODO with a subcategory construction *)
  Lemma _cone_cat: IsCat cone.
  Proof.
    split; intros. 
    - exact: comp1o.
    - exact: compo1.
    - exact: compoA.
    - move=>/=f f' ff g g' gg. exact/comp_eqv.
  Qed.  
  HB.instance Definition _ := _cone_cat. 

  (** * limits *)
  
  Definition is_limit := @terminal cone.
  Definition Limit := Terminal cone.
  
End s.

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃) {𝐄: Cat}.

  (** * lifting functors to cones *)

  Section s.
    Context (G: Functor 𝐃 𝐄).

    Definition Fcone (x: cone F): cone (catcomp F G).
      exists (G (cone_ob x)).
      exists (fun c => Fhom G (cone_mor x c)).
      abstract (move=>c c' f; rewrite -Fcomp; apply:Fhom_eqv; exact: coneP).
    Defined.
    
    Definition Fconehom (x y: cone F) (f: conehom x y): Fcone x ~> Fcone y.
      exists (Fhom G f).
      abstract (move=>c; rewrite -Fcomp; apply:Fhom_eqv; exact: conehomP).
    Defined.
    
    HB.instance Definition _ :=
      @IsFunctor.Build _ _ Fcone Fconehom
        (fun _ _ _ _ H => Fhom_eqv (F:=G) H) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _).
  End s.
  
  (** * lifting (right) adjunctions to cones *)
  
  Section s.
    Context (G: RightAdjoint 𝐃 𝐄).

    Definition Fcone' (x: cone (catcomp F G)): cone F.
      exists (adj G (cone_ob x)).
      exists (fun c => radj.dn (cone_mor x c)).
      move=>c c' f. cbn. sorry.  (* TODO *)
    Defined.
    
    Definition Fcone'hom (x y: cone (catcomp F G)) (f: conehom x y): Fcone' x ~> Fcone' y.
      exists (Fhom (adj G) f).
      move=>c. cbn. sorry.       (* TODO *)
    Defined.
    
    HB.instance Definition _ :=
      @IsFunctor.Build _ _ Fcone' Fcone'hom
        (fun _ _ _ _ H => Fhom_eqv (F:=adj G) H) (fun _ => Fidmap) (fun _ _ _ _ _ => Fcomp _ _).
    
    HB.instance Definition _ := IsPreAdjointF.Build _ _ (Fcone G) Fcone'. 

    Definition Fcone_adj: adjunction Fcone' (Fcone G).
      (* TODO: finish proofs *)
      unshelve esplit. 
      - unshelve esplit.
        move=>/=C. exists (radj.unit G (cone_ob C)).
        move=>/=c. cbn. sorry.
        split; split. move=>/=C D h. cbn. sorry.
      - unshelve esplit.
        move=>/=C. exists (radj.counit G (cone_ob C)).
        move=>/=c. cbn. sorry.
        split; split. move=>/=C D h. cbn. sorry.
      - cbn=>C. sorry.  
      - cbn=>C. sorry.  
    Defined.
    HB.instance Definition _ := IsRightAdjoint.Build _ _ (Fcone G) Fcone_adj.

    (** * right adjoints preserve limits *)
    Theorem radj_preserve_limit (A: cone F): is_limit A -> is_limit (Fcone G A).
    Proof. apply: radj.preserve_terminal. Defined.

  End s.
  
End s.


(** * equivalent diagrams yield equivalent categories of cones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat}.
  Definition transport_cone (F G: Diagram 𝐂 𝐃) (n: F ~> G) (C: cone F): cone G.
  Proof.
    exists (cone_ob C). exists (fun c => cone_mor C c \; n c). sorry. (* composition of natural transformations... *)
  Defined.
  Definition transport_conehom (F G: Diagram 𝐂 𝐃) (n: F ~> G) (C D: cone F) (h: conehom C D):
    conehom (transport_cone n C) (transport_cone n D).
  Proof.
    exists (conehom_sort h). move=>c. cbn. by arewrite conehomP.
  Defined.

  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: F ~> G) :=
    @IsFunctor.Build _ _ (transport_cone n) (transport_conehom n)
      (fun _ _ _ _ H => H) (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).

  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: F ≃ G) :=
    IsPreAdjointF.Build _ _ (transport_cone n) (transport_cone n⁻¹). 

  Definition transport_cone_ladj (F G: Diagram 𝐂 𝐃) (n: F ≃ G):
    adjunction (transport_cone n) (transport_cone n⁻¹).
  Proof.
    unshelve esplit.
    - unshelve esplit. move=>/=C. cbn. exists idmap. cbn=>c. by arewrite (invKr (s:=iso_ntx_pw1 n c)).
      split; split. cbn=>C D f. cat. 
    - unshelve esplit. move=>/=C. cbn. exists idmap. cbn=>c. symmetry; arewrite (invKl (s:=iso_ntx_pw1 n c)). cat. 
      split; split. cbn=>C D f. cat.
    - cbn=>C. cat. 
    - cbn=>C. cat. 
  Defined.
  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: F ≃ G) :=
    IsLeftAdjoint.Build _ _ (transport_cone n) (transport_cone_ladj n). 
  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: F ≃ G) :=
    IsRightAdjoint.Build _ _ (transport_cone n) (transport_cone_ladj n⁻¹). 
  HB.instance Definition _ (F G: Diagram 𝐂 𝐃) (n: F ≃ G) :=
    IsAdjointEquivalence.Build _ _ (transport_cone n). 
End s.


(** * creating limits through right coreflections *)

Definition limits (S: BareQuiver) (𝐂: Cat) := forall D: Diagram S 𝐂, Limit D.

Section s.  
  Context {𝐂 𝐃: Cat} (F: RightCoreflection 𝐂 𝐃) (S: BareQuiver).
  Hypothesis lim: limits S 𝐂.
  Section s.
    Variable D: Diagram S 𝐃.
    Let limC := lim (catcomp D (adj F)).
    Let limD' := Fcone F (TERMINAL.sort limC).
    Let limit_limD': is_limit limD' := radj_preserve_limit (G:=F) (terminalP (s:=limC)).    
    Let n: ((D \; adj F \; F)%FUN: Diagram _ _) ≃ D.
    Proof.
      (* TOIMPROVE: intuitively: ntx_comp' (ntx_id D) (rcorefl.unit F) *)
      apply/iso_sym.
      unshelve apply: iso_ntx.
      - move=>c. exact: (rcorefl.unit F (D c): _ ≃ _).
      - cbn=>c d f. exact: (natural (rcorefl.unit F) (Fhom D f)). 
    Defined.
    Let limD: cone D := transport_cone n limD'.
    Let limit_limD: is_limit limD := (radj.preserve_terminal (transport_cone n) limit_limD').
    HB.instance Definition _ := IsTerminal.Build (cone D) limD limit_limD.
  End s.
  Theorem rcorefl_create_limits: limits S 𝐃.
  Proof. exact: limit_limD__canonical__cat_TERMINAL. Defined.
End s.


(** * HB packaging *)


(** ** categories with all limits of shape [S] *)
#[primitive] HB.mixin Record HasLimits (S: BareQuiver) 𝐂 & CAT 𝐂 := 
  { #[canonical=no] lim: limits S 𝐂 }.

#[short(type="CatLim")]
HB.structure Definition CATLIM (S: BareQuiver) := { 𝐂 of HasLimits S 𝐂 & }.

HB.factory Record HasLimitsThroughAdj S (𝐃: CatLim S) 𝐂 & CAT 𝐂 := { F: RightCoreflection 𝐃 𝐂 }.
HB.builders Context S 𝐃 𝐂 & HasLimitsThroughAdj S 𝐃 𝐂.
HB.instance Definition _ := HasLimits.Build S 𝐂 (rcorefl_create_limits F lim).
HB.end.
