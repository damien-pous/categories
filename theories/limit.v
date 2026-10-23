(** cones and limits *)

Require Import cat functor adjunction.
Require Import arewrite.

Open Scope cat_scope.

(** * cones *)

Section s.
  Context {𝐂: BareQuiver} {𝐃: Cat} (F: Diagram 𝐂 𝐃).
  
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

    HB.instance Definition _ (A: Limit F) :=
      IsTerminal.Build _ (Fcone G (TERMINAL.sort A)) (radj_preserve_limit terminalP). 
  End s.
  
  Section s.
    Context (G: AdjointEquivalence 𝐃 𝐄).
    (* TODO: declare [Fcone G] as an adjoint equivalence, through proper factories *)
  End s.
  
End s.

