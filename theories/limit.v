(** cones and limits *)

Require Export functor adjunction.
Require Import arewrite.

Local Open Scope cat_scope.

(** * cones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃).
  
  Definition cone := {C & {p: forall c, F c ~> C | forall c c' (f: c ~> c'), Fhom F f \; p c' ≡ p c }}.
  Definition cone_ob (C: cone): ob 𝐃 := projT1 C. 
  Definition cone_mor (C: cone): forall c, F c ~> cone_ob C := proj1_sig (projT2 C). 
  Lemma coneP (C: cone) c c' (f: c ~> c'): Fhom F f \; cone_mor C c' ≡ cone_mor C c.
  Proof. exact: (proj2_sig (projT2 C)). Qed.

  Definition conehom (C D: cone) :=
    { h: cone_ob C ~> cone_ob D | forall c, cone_mor C c \; h ≡ cone_mor D c }.
  Coercion conehom_sort C D: conehom C D -> (cone_ob C ~> cone_ob D) := @proj1_sig _ _. 
  Lemma conehomP C D (h: conehom C D) c: cone_mor C c \; h ≡ cone_mor D c.
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
  
  Definition is_limit := @initial cone.
  Definition Limit := Initial cone.
  
End s.

(** * lifting functors to cones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃) {𝐄: Cat}.

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
  
  (** * lifting (left) adjunctions to cones *)
  
  Section s.
    Context (G: LeftAdjoint 𝐃 𝐄).

    Definition Fcone' (x: cone (catcomp F G)): cone F.
      exists (adj G (cone_ob x)).
      exists (fun c => ladj.up (cone_mor x c)).
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
    HB.instance Definition _ := IsPreAdjointF.Build _ _ Fcone' (Fcone G).

    Definition Fcone_adj: adjunction (Fcone G) Fcone'.
      (* TODO: finish proofs *)
      unshelve esplit. 
      - unshelve esplit.
        move=>/=C. exists (ladj.unit G (cone_ob C)).
        move=>/=c. cbn. sorry.
        split; split. move=>/=C D h. cbn. sorry.
      - unshelve esplit.
        move=>/=C. exists (ladj.counit G (cone_ob C)).
        move=>/=c. cbn. sorry.
        split; split. move=>/=C D h. cbn. sorry.
      - cbn=>C. sorry.  
      - cbn=>C. sorry.  
    Defined.
    HB.instance Definition _ := IsLeftAdjoint.Build _ _ (Fcone G) Fcone_adj.
    HB.instance Definition _ := IsRightAdjoint.Build _ _ Fcone' Fcone_adj.

    (** * left adjoints preserve limits *)
    Theorem ladj_preserve_limit (A: cone F): is_limit A -> is_limit (Fcone G A).
    Proof. apply: ladj.preserve_initial. Defined.

    HB.instance Definition _ (A: Limit F) :=
      IsInitial.Build _ (Fcone G (INITIAL.sort A)) (ladj_preserve_limit initialP). 
  End s.
  
  Section s.
    Context (G: AdjointEquivalence 𝐃 𝐄).
    (* TODO: declare [Fcone G] as an adjoint equivalence, through proper factories *)
  End s.
  
End s.

