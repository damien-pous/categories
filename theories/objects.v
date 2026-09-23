(** structures on objects *)

Require Export functor.
Require Import arewrite.
From elpi Require Import elpi coercion.

Local Open Scope cat_scope.

Definition ob (C: Type) := C.

(** * initial/terminal objects *)

Definition is_initial {𝐂: Quiver} (A: 𝐂) :=
  forall X, Σ!_: A~>X, True.
Definition is_terminal {𝐂: Quiver} (A: 𝐂) :=
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

Check fun (C: Quiver) (A: Initial C) => A: ob C.
Check fun (C: PreCat) (A: Initial C) => A: ob C.
Check fun (C: Cat) (A: Initial C) => A: ob C.

Definition obop (𝐂: Quiver) (A: ob 𝐂): ob 𝐂^op := A. 

HB.instance Definition _ (𝐂: Quiver) (A: Initial 𝐂) :=
  IsTerminal.Build 𝐂^op (obop A) (@initial_prop _ A).
HB.instance Definition _ (𝐂: Quiver) (A: Terminal 𝐂) :=
  IsInitial.Build 𝐂^op (obop A) (@terminal_prop _ A).

Check fun (C: Quiver) (A: Initial C) => obop A: Terminal (C^op).
Check fun (C: PreCat) (A: Initial C) => obop A: Terminal (C^op).
Check fun (C: Cat) (A: Initial C) => obop A: Terminal (C^op).


(* Elpi Accumulate coercion.db lp:{{  *)
(*       coercion _ V T E R :-  *)
(*       coq.unify-eq T {{quiver.sort _}} ok,  *)
(*       coq.unify-eq E {{@initial_ob.type lp:C}} ok,  *)
(*       !, *)
(*       coq.unify-eq V {{@initial_ob.sort lp:C lp:W}} ok, *)
(*       R = {{ @reverse_coercion lp:E lp:T lp:W lp:V }}. *)
(*       coercion _ V T E R :-  *)
(*       coq.unify-eq T {{quiver.sort _}} ok,  *)
(*       coq.unify-eq E {{@terminal_ob.type lp:C}} ok,  *)
(*       !, *)
(*       coq.unify-eq V {{@terminal_ob.sort lp:C lp:W}} ok, *)
(*       R = {{ @reverse_coercion lp:E lp:T lp:W lp:V }}. *)
(*       }}. *)
    
(* (* TODO: move to tests *) *)
(*     Check fun (C: Quiver) (A: Initial C) => A: C. (* reversible coercion *) *)
(* Check fun (C: PreCat) (A: Initial C) => A: C. *)
(* Fail Check fun (C: PreCat) (A: Initial C) => initial_ob.sort A: C. *)
(* Fail Check fun (C: Cat) (A: Initial C) => A: C. *)
(* Check fun (C: Quiver) (A: Initial C) => obop A: Terminal (C^op). *)
(* Check fun (C: PreCat) (A: Initial C) => obop A: Terminal (C^op). *)
(* Check fun (C: Cat) (A: Initial C) => obop A: Terminal (C^op). *)

Definition initial (𝐂: Quiver) (A: Initial 𝐂) X: A ~> X := unique_morph (initial_prop X).
Definition terminal (𝐂: Quiver) (A: Terminal 𝐂) X: X ~> A := unique_morph (terminal_prop X).

Lemma initialU (𝐂: Quiver) (A: Initial 𝐂) X (f g: A ~> X): f ≡ g.
Proof. apply: Unicity. exact: (initial_prop X). all: done. Qed.
Lemma terminalU (𝐂: Quiver) (A: Terminal 𝐂) X (f g: X ~> A): f ≡ g.
Proof.
  move: (@initialU (𝐂^op) (obop A) (obop X) (morphop f) (morphop g)).
  apply: Unicity. exact: (terminal_prop X). all: done. 
Qed.

Definition iso_Initial (𝐂: Cat) (A B: Initial 𝐂): initial_ob.sort A ≃_𝐂 initial_ob.sort B :=
  mk_iso (initial A B) (initial B A) (initialU _ _) (initialU _ _).
Definition iso_Terminal (𝐂: Cat) (A B: Terminal 𝐂): terminal_ob.sort A ≃_𝐂 terminal_ob.sort B :=
  mk_iso (terminal B A) (terminal A B) (terminalU _ _) (terminalU _ _).

(* useful? *)
Lemma InitialU (𝐂: PreCat) (A B: Initial 𝐂) (i j: initial_ob.sort A ≃_𝐂 initial_ob.sort B): i ≡ j.
Proof. exact: initialU. Qed.
Lemma TerminalU (𝐂: PreCat) (A B: Terminal 𝐂) (i j: terminal_ob.sort A ≃_𝐂 terminal_ob.sort B): i ≡ j.
Proof. exact: terminalU. Qed.

(** * squares *)

(** the category of morphisms and squares *)

Definition morphism (𝐂: Quiver) := { A: 𝐂 & {B: 𝐂 & A ~> B }}.
Definition src {𝐂} (f: morphism 𝐂): 𝐂 := projT1 f. 
Definition tgt {𝐂} (f: morphism 𝐂): 𝐂 := projT1 (projT2 f). 
Coercion mor {𝐂} (f: morphism 𝐂): src f ~> tgt f := projT2 (projT2 f).
Definition Mor {𝐂: Quiver} {A B: 𝐂} (f: A ~> B): morphism 𝐂 := existT _ A (existT _ B f).

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


(** * (co)algebras *)

#[primitive]
HB.mixin Record IsAlgebra {𝐂: Quiver} (F: 𝐂 -> 𝐂) (A: 𝐂) := {
    #[canonical=no] alg: F A ~> A;
  }.
#[short(type="Algebra")]
HB.structure Definition algebra 𝐂 F := { A of IsAlgebra 𝐂 F A }.
Arguments alg {_ _ _}, {_ _}. 

(* TOTHINK: do we really want to infer algebra homomorphisms, or just define them? *)
#[primitive]
HB.mixin Record IsAlgebraHom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F) (f: A ~> B) := {
    #[canonical=no] alg_hom: Fhom F f \; alg B ≡ alg A \; f;
  }.
#[short(type="AlgebraHom")]
HB.structure Definition algebrahom 𝐂 F A B := { f of IsAlgebraHom 𝐂 F A B f }.
Arguments alg_hom {_ _ _ _ _}, {_ _ _ _}. 
Arguments AlgebraHom {_ _}, {_}. 

HB.instance Definition _ 𝐂 F A B := Setoid.copy (AlgebraHom F A B) (kernel (@algebrahom.sort 𝐂 F A B)).
HB.instance Definition _ (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (Algebra F) AlgebraHom.

Lemma _algebrahom_idmap (𝐂: Cat) (F: Functor 𝐂 𝐂) (A: Algebra F): IsAlgebraHom _ F A A idmap.
Proof. split. cat. Qed.
HB.instance Definition _ 𝐂 F A := @_algebrahom_idmap 𝐂 F A.

Lemma _algebrahom_comp (𝐂: Cat) (F: Functor 𝐂 𝐂) (A B C: Algebra F) (f: A ~> B) (g: B ~> C): IsAlgebraHom _ F A C (f \; g).
Proof. split. rewrite Fcomp. do 2 arewrite alg_hom. cat. Qed.
HB.instance Definition _ 𝐂 F A B C f g := @_algebrahom_comp 𝐂 F A B C f g.

(* TOTHINK: set arguments so that they always unfold? *)
Definition alg_id {𝐂: Cat} {F: Functor 𝐂 𝐂} (A: Algebra F): A ~> A := idmap: AlgebraHom _ _. 
Definition alg_comp {𝐂: Cat} {F: Functor 𝐂 𝐂} (A B C: Algebra F) (f: A ~> B) (g: B ~> C): A ~> C := f \; g: AlgebraHom _ _. 

HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) := IsPreCat.Build (Algebra F) alg_id alg_comp.

(* below: rather convoluted proof that Algebras form a category, by faithful embedding into the category of morphisms and squares... *)
Definition _alg_morphism (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) (A: Algebra F): morphism 𝐂 := Mor (alg A).
Arguments _alg_morphism {_}. 
Program Definition _alg_morphism_prefunctor (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) :=
  @IsFaithfulPreFunctor.Build (Algebra F) (morphism 𝐂)
    (_alg_morphism F)
    (fun A B f => @Square _ (Mor (alg A)) (Mor (alg B)) _ _ (alg_hom f)) _.
Next Obligation. split. exact/snd. split=>//. exact/Fhom_eqv. Qed.
HB.instance Definition _ (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) := _alg_morphism_prefunctor F. 
Program Definition _alg_morphism_functor (𝐂: Cat) (F: Functor 𝐂 𝐂) :=
  IsFunctor.Build (Algebra F) (morphism 𝐂) (_alg_morphism F) _ _.
Next Obligation. intros. split=>//=. cat. Qed.
Next Obligation. intros. split=>//=. cat. Qed.
HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) := _alg_morphism_functor F. 

HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) :=
  FaithfulSubCat.Build (morphism 𝐂) (Algebra F) (_alg_morphism F).

Section s.
  Context {𝐂: Quiver} (F: PreFunctor 𝐂 𝐂) (A: Algebra F).
  Check A: 𝐂.
End s.
Section s.  
  Context {𝐂: Cat} (F: Functor 𝐂 𝐂) (A: Algebra F).
  Fail Check A: 𝐂.
  Check algebra.sort A: 𝐂.
  Check alg A: F A ~> A.
  Check alg: F A ~> A.
End s.


Definition funcop {A B} (f: A -> B): A^op -> B^op := f. 
HB.instance Definition _ 𝐂 𝐃 (F: PreFunctor 𝐂 𝐃) :=
  @IsPreFunctor'.Build 𝐂^op 𝐃^op (funcop F) (fun _ _ f => Fhom F f)
                                (fun A B f g fg => @Fhom_eqv _ _ F B A f g fg).
HB.instance Definition _ 𝐂 𝐃 (F: Functor 𝐂 𝐃) :=
  @IsFunctor.Build 𝐂^op 𝐃^op (funcop F) (fun _ => Fidmap _) (fun _ _ _ _ _ => Fcomp _ _ _ _ _). 

#[primitive]
HB.mixin Record IsCoAlgebra {𝐂: Quiver} (F: 𝐂 -> 𝐂) (A: 𝐂) := {
    #[canonical=no] coalg: A ~> F A;
  }.
#[short(type="CoAlgebra")]
HB.structure Definition coalgebra 𝐂 F := { A of IsCoAlgebra 𝐂 F A }.
Arguments coalg {_ _ _}, {_ _}. 


HB.instance Definition _ {𝐂: Quiver} (F: PreFunctor 𝐂 𝐂) (A: Algebra F) :=
  IsCoAlgebra.Build (𝐂^op) (funcop F) (obop A) (alg A).
HB.instance Definition _ {𝐂: Quiver} (F: PreFunctor 𝐂 𝐂) (A: CoAlgebra F) :=
  IsAlgebra.Build (𝐂^op) (funcop F) (obop A) (coalg A).

Check fun (C: Quiver) (F: C -> C) (A: CoAlgebra F) => C^op: Quiver.  
Check fun (C: Quiver) (F: C -> C) (A: CoAlgebra F) => funcop F: C^op -> C^op.  
Check fun (C: Quiver) (F: C -> C) (A: CoAlgebra F) => obop A: C^op.
Check fun (C: Quiver) (F: C -> C) (A: CoAlgebra F) => obop A: Algebra _.  
Check fun (C: Quiver) (F: C -> C) (A: CoAlgebra F) => obop A: @Algebra (C^op) (funcop F).  
Fail Check fun (C: Quiver) (F: C -> C) (A: Algebra F) => obop A: CoAlgebra _.


#[primitive]
HB.mixin Record IsCoAlgebraHom {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: CoAlgebra F) (f: A ~> B) := {
    #[canonical=no] coalg_hom: coalg A \; Fhom F f ≡ f \; coalg B;
  }.
#[short(type="CoAlgebraHom")]
HB.structure Definition coalgebrahom 𝐂 F A B := { f of IsCoAlgebraHom 𝐂 F A B f }.
Arguments coalg_hom {_ _ _ _ _}, {_ _ _ _}. 
Arguments CoAlgebraHom {_ _}, {_}. 

HB.instance Definition _ {𝐂: PreCat} (F: PreFunctor 𝐂 𝐂) (A B: Algebra F) (f: A ~> B) :=
  IsCoAlgebraHom.Build (𝐂^op) (funcop F) (obop B) (obop A) (morphop f) (alg_hom f).


HB.instance Definition _ 𝐂 F A B := Setoid.copy (CoAlgebraHom F A B) (kernel (@coalgebrahom.sort 𝐂 F A B)).
HB.instance Definition _ (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) := IsQuiver.Build (CoAlgebra F) CoAlgebraHom.

Lemma _algebrahom_idmap (𝐂: Cat) (F: Functor 𝐂 𝐂) (A: Algebra F): IsAlgebraHom _ F A A idmap.
Proof. split. cat. Qed.
HB.instance Definition _ 𝐂 F A := @_algebrahom_idmap 𝐂 F A.

Lemma _algebrahom_comp (𝐂: Cat) (F: Functor 𝐂 𝐂) (A B C: Algebra F) (f: A ~> B) (g: B ~> C): IsAlgebraHom _ F A C (f \; g).
Proof. split. rewrite Fcomp. do 2 arewrite alg_hom. cat. Qed.
HB.instance Definition _ 𝐂 F A B C f g := @_algebrahom_comp 𝐂 F A B C f g.

(* TOTHINK: set arguments so that they always unfold? *)
Definition alg_id {𝐂: Cat} {F: Functor 𝐂 𝐂} (A: Algebra F): A ~> A := idmap: AlgebraHom _ _. 
Definition alg_comp {𝐂: Cat} {F: Functor 𝐂 𝐂} (A B C: Algebra F) (f: A ~> B) (g: B ~> C): A ~> C := f \; g: AlgebraHom _ _. 

HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) := IsPreCat.Build (Algebra F) alg_id alg_comp.

(* below: rather convoluted proof that Algebras form a category, by faithful embedding into the category of morphisms and squares... *)
Definition _alg_morphism (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) (A: Algebra F): morphism 𝐂 := Mor (alg A).
Arguments _alg_morphism {_}. 
Program Definition _alg_morphism_prefunctor (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) :=
  @IsFaithfulPreFunctor.Build (Algebra F) (morphism 𝐂)
    (_alg_morphism F)
    (fun A B f => @Square _ (Mor (alg A)) (Mor (alg B)) _ _ (alg_hom f)) _.
Next Obligation. split. exact/snd. split=>//. exact/Fhom_eqv. Qed.
HB.instance Definition _ (𝐂: PreCat) (F: PreFunctor 𝐂 𝐂) := _alg_morphism_prefunctor F. 
Program Definition _alg_morphism_functor (𝐂: Cat) (F: Functor 𝐂 𝐂) :=
  IsFunctor.Build (Algebra F) (morphism 𝐂) (_alg_morphism F) _ _.
Next Obligation. intros. split=>//=. cat. Qed.
Next Obligation. intros. split=>//=. cat. Qed.
HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) := _alg_morphism_functor F. 

HB.instance Definition _ (𝐂: Cat) (F: Functor 𝐂 𝐂) :=
  FaithfulSubCat.Build (morphism 𝐂) (Algebra F) (_alg_morphism F).





(** * cones/cocones *)

Section s.
  Context {𝐃: Quiver} {𝐂: PreCat} (F: PreFunctor 𝐃 𝐂).
  Definition cone := {C & {p: forall d, F d ~> C | forall d d' (f: d ~> d'), Fhom F f \; p d' ≡ p d }}.
  Definition cone_ob (C: cone): 𝐂 := projT1 C. 
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
  Program Definition _cone_cat :=
    IsCat.Build (cone F) _ _ _ _.
  Next Obligation. move=>*. exact: comp1o. Qed.
  Next Obligation. move=>*. exact: compo1. Qed.
  Next Obligation. move=>*. exact: compoA. Qed.
  Next Obligation. move=>C D E/=f f' ff g g' gg. exact: comp_eqv. Qed.  
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

From Stdlib Require Export CMorphisms.

Section s.
  Context {𝐂: Quiver}.
  Variables A B: 𝐂.
  Definition ob_pair (d: DiscreteTwo) := if d then B else A.
  HB.instance Definition _ := IsPreFunctor.Build _ _ ob_pair (fun _ _ => empty_fun).
End s.
Section s.
  Context {𝐂: PreCat}.
  Variables A B: 𝐂.
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
                    
End s.. 

Definition ParallelTwo := bool.
Definition paralleltwo_hom (a b: ParallelTwo): StrictSetoid.type :=
  match a,b with
  | false,true => bool
  | _,_ => False
  end.
HB.instance Definition _ := IsQuiver.Build ParallelTwo paralleltwo_hom.   
  

Section s.
  Context {𝐂: Quiver}.
  Variables A B: 𝐂.
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
  | None,Some _ => unit
  | _,_ => False
  end.
Definition Span := Three.
HB.instance Definition _ := IsQuiver.Build Span span_hom.

Section s.
  Context {𝐂: Quiver}.
  Variables A B C: 𝐂.
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
Check CoSpan: Quiver.
