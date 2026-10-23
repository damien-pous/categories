(** cocones and colimits *)

Require Import cat functor adjunction limit.
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
  
  Section s.
    Context (G: AdjointEquivalence 𝐃 𝐄).
    (* TODO: declare [Fcocone G] as an adjoint equivalence, through proper factories *)
  End s.
  
End s.

