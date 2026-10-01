(** structures on objects *)

Require Export functor.
Require Import arewrite.
Require Import adjunction.
From Stdlib Require Import CMorphisms.

Local Open Scope cat_scope.

(** * initial/terminal objects *)

Definition is_initial {𝐂: Quiver} (A: ob 𝐂) :=
  forall X, Σ!_: A~>X, True.
Definition is_terminal {𝐂: Quiver} (A: ob 𝐂) :=
  forall X, Σ!_: X~>A, True.

#[primitive]
HB.mixin Record IsInitial (𝐂: Quiver) (A: ob 𝐂) := {
    #[canonical=no] initial_prop: is_initial A 
  }.
#[short(type="Initial")]
HB.structure Definition initial_ob 𝐂 := { A of IsInitial 𝐂 A }.

#[primitive]
HB.mixin Record IsTerminal (𝐂: Quiver) (A: ob 𝐂) := {
    #[canonical=no] terminal_prop: is_terminal A
  }.
#[short(type="Terminal")]
HB.structure Definition terminal_ob 𝐂 := { A of IsTerminal 𝐂 A }.

(* Check fun (C: Quiver) (A: Initial C) => A: ob C. *)
(* Check fun (C: PreCat) (A: Initial C) => A: ob C. *)
(* Check fun (C: Cat) (A: Initial C) => A: ob C. *)

HB.instance Definition _ (𝐂: Quiver) (A: Initial 𝐂) :=
  IsTerminal.Build 𝐂^op (obop A) (@initial_prop _ A).
HB.instance Definition _ (𝐂: Quiver) (A: Terminal 𝐂) :=
  IsInitial.Build 𝐂^op (obop A) (@terminal_prop _ A).

(* Check fun (C: Quiver) (A: Initial C) => obop A: Terminal (C^op). *)
(* Check fun (C: PreCat) (A: Initial C) => obop A: Terminal (C^op). *)
(* Check fun (C: Cat) (A: Initial C) => obop A: Terminal (C^op). *)

Definition initial (𝐂: Quiver) (A: Initial 𝐂) X: A ~> X := unique_morph (initial_prop X).
Definition terminal (𝐂: Quiver) (A: Terminal 𝐂) X: X ~> A := unique_morph (terminal_prop X).

Lemma initialU (𝐂: Quiver) (A: Initial 𝐂) X (f g: A ~> X): f ≡ g.
Proof. apply: Unicity. exact: (initial_prop X). all: done. Qed.
Lemma terminalU (𝐂: Quiver) (A: Terminal 𝐂) X (f g: X ~> A): f ≡ g.
Proof. exact: (initialU (morphop f) (morphop g)). Qed.

Definition iso_Initial (𝐂: Cat) (A B: Initial 𝐂): A ≃ B :=
  mk_iso (initial A B) (initial B A) (initialU _ _) (initialU _ _).
Definition iso_Terminal (𝐂: Cat) (A B: Terminal 𝐂): A ≃ B :=
  mk_iso (terminal B A) (terminal A B) (terminalU _ _) (terminalU _ _).

(* useful? *)
Lemma InitialU (𝐂: PreCat) (A B: Initial 𝐂) (i j: A ≃ B): i¹ ≡ j¹.
Proof. exact: initialU. Qed.
Lemma TerminalU (𝐂: PreCat) (A B: Terminal 𝐂) (i j: A ≃ B): i¹ ≡ j¹.
Proof. exact: terminalU. Qed.

Lemma adjoint_preserve_initial (𝐂 𝐃: Cat) (F: 𝐂 ⊣ 𝐃) (A: ob 𝐂) (H: is_initial A): is_initial (F A).
Proof.
  move=>X. destruct (H (radj F X)) as [f _ U].
  exists (dn f)=>//g _. specialize (U (up g) I). apply: up_inj. by rewrite up_dn.
Qed.
(* forgetful inheritance?, why? *)
HB.instance Definition _ (𝐂 𝐃: Cat) (F: 𝐂 ⊣ 𝐃) (A: Initial 𝐂) :=
  IsInitial.Build 𝐃 (F A) (adjoint_preserve_initial F initial_prop).

(** * squares *)

(** the category of morphisms and squares *)

Definition morphism (𝐂: Quiver) := { A: ob 𝐂 & {B: ob 𝐂 & A ~> B }}.
Definition src {𝐂} (f: morphism 𝐂): ob 𝐂 := projT1 f. 
Definition tgt {𝐂} (f: morphism 𝐂): ob 𝐂 := projT1 (projT2 f). 
Coercion mor {𝐂} (f: morphism 𝐂): src f ~> tgt f := projT2 (projT2 f).
Definition Mor {𝐂: Quiver} {A B: ob 𝐂} (f: A ~> B): morphism 𝐂 := existT _ A (existT _ B f).

Definition square {𝐂: PreCat} (f g: morphism 𝐂) :=
  { i: src f ~> src g & { j: tgt f ~> tgt g | i \; g ≡ f \; j }}.
Definition square_src {𝐂: PreCat} (f g: morphism 𝐂) (h: square f g) := projT1 h. 
Definition square_tgt {𝐂: PreCat} (f g: morphism 𝐂) (h: square f g) := proj1_sig (projT2 h). 
Definition squareP {𝐂: PreCat} (f g: morphism 𝐂) (h: square f g): square_src h \; g ≡ f \; square_tgt h := proj2_sig (projT2 h).
Definition Square {𝐂: PreCat} {f g: morphism 𝐂} (i: src f ~> src g) (j: tgt f ~> tgt g) (P: i \; g ≡ f \; j): square f g := existT _ i (exist _ j P).

HB.instance Definition _ (𝐂: PreCat) (f g: morphism 𝐂) :=
  Setoid.copy (square f g) (kernel (fun h => (square_src h, square_tgt h))).
HB.instance Definition _ (𝐂: PreCat) := IsQuiver.Build (morphism 𝐂) square.

Definition square_id {𝐂: Cat} (f: morphism 𝐂): f ~> f.
  exists idmap, idmap. abstract cat.
Defined.

Definition square_comp {𝐂: Cat} (f g h: morphism 𝐂) (i: f ~> g) (j: g ~> h): f ~> h.
  exists (square_src i\;square_src j), (square_tgt i\;square_tgt j).
  abstract (do 2 arewrite squareP; cat). 
Defined.

HB.instance Definition _ (𝐂: Cat) := IsPreCat.Build (morphism 𝐂) square_id square_comp.

Lemma _square_cat (𝐂: Cat):  IsCat (morphism 𝐂).
Proof.
  split. 
  split=>/=; exact: comp1o.
  split=>/=; exact: compo1.
  split=>/=; exact: compoA.
  move=>f g h i i' [i1 i2] j j' [j1 j2]; split; exact/comp_eqv.
Qed.
HB.instance Definition _ 𝐂 := _square_cat 𝐂. 


    



(** * cones/cocones *)

Section s.
  Context {𝐃: Quiver} {𝐂: PreCat} (F: PreFunctor 𝐃 𝐂).
  Definition cone := {C & {p: forall d, F d ~> C | forall d d' (f: d ~> d'), Fhom F f \; p d' ≡ p d }}.
  Definition cone_ob (C: cone): ob 𝐂 := projT1 C. 
  Definition cone_mor (C: cone): forall d, F d ~> cone_ob C := proj1_sig (projT2 C). 
  Lemma coneP (C: cone) d d' (f: d ~> d'): Fhom F f \; cone_mor C d' ≡ cone_mor C d.
  Proof. exact: (proj2_sig (projT2 C)). Qed.

  Definition cone_hom (C D: cone) :=
    { h: cone_ob C ~> cone_ob D | forall d, cone_mor C d \; h ≡ cone_mor D d }.
  Coercion cone_hom_ C D: cone_hom C D -> (cone_ob C ~> cone_ob D) := @proj1_sig _ _. 
  Lemma cone_homP C D (h: cone_hom C D) d: cone_mor C d \; h ≡ cone_mor D d.
  Proof. exact: (proj2_sig h). Qed.
  
  HB.instance Definition _ := IsQuiver.Build cone cone_hom.

  Definition is_limit := @is_initial cone.
  Definition limit := Initial cone.
End s.
Section s.
  Context {𝐃: Quiver} {𝐂: Cat} (F: PreFunctor 𝐃 𝐂).

  Program Definition cone_id (C: cone F): C ~> C := exist _ idmap _.
  Next Obligation. move=>/=C d. cat. Qed.
  Program Definition cone_comp (C D E: cone F) (f: C ~> D) (g: D ~> E): C ~> E :=
    exist _ (f \; g) _.
  Next Obligation.
    move=>C D E f g d. arewrite cone_homP. exact/cone_homP.
  Qed.
  HB.instance Definition _ := IsPreCat.Build (cone F) (@cone_id) (@cone_comp).

  (* TODO with a subcategory construction *)
  Lemma _cone_cat: IsCat (cone F).
  Proof.
    split; intros. 
    - exact: comp1o.
    - exact: compo1.
    - exact: compoA.
    - move=>/=f f' ff g g' gg. exact/comp_eqv.
  Qed.  
  HB.instance Definition _ := _cone_cat. 

End s.

Definition EmptyQuiver (T: Type) := T.
HB.instance Definition _ T := IsQuiver.Build (EmptyQuiver T) (fun _ _ => False). 

Definition Cat0 := EmptyQuiver False.
HB.instance Definition _ := quiver.on Cat0. 
HB.instance Definition _ := IsPreCat.Build Cat0 empty_fun (fun a => @empty_fun _ a). 
Program Definition _cat0 := IsCat.Build Cat0 _ _ _ _.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
HB.instance Definition _ := _cat0.

Module Shape.

Definition DiscreteTwo := bool.
HB.instance Definition _ := quiver.copy DiscreteTwo (EmptyQuiver _). 


Section s.
  Context {𝐂: Quiver}.
  Variables A B: ob 𝐂.
  Definition ob_pair (d: DiscreteTwo) := if d then B else A.
  HB.instance Definition _ := IsPreFunctor.Build _ _ ob_pair (fun _ _ => empty_fun).
End s.
Section s.
  Context {𝐂: PreCat}.
  Variables A B: ob 𝐂.
  Definition ob_pair_cone C (f: A ~> C) (g: B ~> C): cone (ob_pair A B).
    exists C. unshelve eexists. case=>/=. exact: g. exact: f.
    by case.
  Defined.
    
  Lemma sumL: forall C (f: A ~> C) (g: B ~> C),
      iffT
        (is_limit (ob_pair_cone f g))
        (forall C' (f': A ~> C') (g': B ~> C'), Σ! h: C ~> C', f \; h ≡ f' /\ g \; h ≡ g').
  Proof.
    split.
    - move=>L C' f' g'. destruct (L (ob_pair_cone f' g')) as [[h H] _ U].
      exists h. exact: (conj (H false) (H true)).
      cbn in *=>h' H'. apply: (U (exist _ h' _))=>//.
      case; apply H'.
    - move=> H [C' [p U]].       (* ok and boring *)
  Abort.
                    
End s. 

Definition ParallelTwo := bool.
Definition paralleltwo_hom (a b: ParallelTwo): StrictSetoid.type :=
  match a,b with
  | false,true => bool
  | _,_ => False
  end.
HB.instance Definition _ := IsQuiver.Build ParallelTwo paralleltwo_hom.   
  

Section s.
  Context {𝐂: Quiver}.
  Variables A B: ob 𝐂.
  Definition parallel_pair (_ _: A ~> B) (d: ParallelTwo) := if d then B else A.
  Variables f g: A ~> B.
  Definition Fparallel_pair (d d': ParallelTwo): (d ~> d') -> parallel_pair f g d ~> parallel_pair f g d' :=
    match d,d' with
    | false,true => fun b => if b then g else f
    | _,_ => empty_fun
    end.
  HB.instance Definition _ d d' := StrictThusExtensional.Build _ _ (@Fparallel_pair d d'). 
  HB.instance Definition _ := IsPreFunctor.Build _ _ (parallel_pair f g) Fparallel_pair.
End s.

Definition Three := option bool.
Definition span_hom (a b: Three): StrictSetoid.type :=
  match a,b with
  | None,Some _ => Datatypes.unit
  | _,_ => False
  end.
Definition Span := Three.
HB.instance Definition _ := IsQuiver.Build Span span_hom.

Section s.
  Context {𝐂: Quiver}.
  Variables A B C: ob 𝐂.
  Definition span (_: B ~> A) (_: B ~> C) (d: Span) :=
    match d with
    | None => B
    | Some d => if d then C else A
    end.
  Variables (f: B ~> A) (g: B ~> C).
  Definition Fspan (d d': Span): (d ~> d') -> span f g d ~> span f g d' :=
    match d,d' with
    | None,Some false => fun _ => f
    | None,Some true => fun _ => g
    | _,_ => empty_fun
    end.
  HB.instance Definition _ d d' := StrictThusExtensional.Build _ _ (@Fspan d d'). 
  HB.instance Definition _ := IsPreFunctor.Build _ _ (span f g) Fspan.
End s.


Definition CoSpan := Span^op.
(* HB.instance Definition _ := quiver.on CoSpan.  *)
(* Check CoSpan: Quiver. *)

End Shape.
