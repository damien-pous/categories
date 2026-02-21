(** * MacLane's coherence theorem for monoidal categories

   this proof is largely inspired from the one by Ilya Beylin
   and Peter Dybjer in
   "Extracting a proof of coherence for monoidal categories
    from a formal proof of normalisation for monoids"
   in Proc. TYPES'95
   https://dl.acm.org/doi/10.5555/1813347.1813350 

 *)

Require Import arity monoidal_def.
From elpi Require Import elpi coercion.

Local Open Scope cat_scope.

Section t.

Variable X: Type.

(** tensor-unit expressions, i.e., trees of objects,
    (the type [M] in Ilya Beylin and Peter Dybjer's paper) *)
Inductive tree :=
| t_ob: X -> tree
| t_unit: tree
| t_tensor: tree -> tree -> tree.
Implicit Types a b c: tree.
Notation "1" := t_unit. 
Infix "⊗" := t_tensor. 

(** object normal forms (the type [N] in Ilya Beylin and Peter Dybjer's paper)  *)
Implicit Types n m: arity X.

Definition norm := arity X -> arity X.
Implicit Types x y: norm.
Definition n_id: norm := fun n => n.
Definition n_tensor (x y: norm): norm := fun n => x (y n).
Arguments n_tensor _ _ _/.

Fixpoint arity_tree n :=
  match n with
  | nil => 1
  (* | cons x nil => t_ob x *)
  | cons x n => t_ob x ⊗ arity_tree n
  end.
(* Arguments arity_tree: simpl nomatch. *)
Coercion arity_tree: arity >-> tree.

(** function [| |]: M -> N^N from
    Ilya Beylin and Peter Dybjer's paper *)
Fixpoint Norm a: norm :=
  match a with
  | t_ob x => cons x
  | 1 => n_id
  | a⊗b => n_tensor (Norm a) (Norm b)
  end.

(** We write this function as a second tensor since it behaves like tensor *)
Infix "⊙" := Norm (at level 31, right associativity). 

(** syntax for MacLane morphisms, from one tree to another *)
Inductive maclane: tree -> tree -> Type :=
(* | mcl_var: forall x, maclane (t_ob x) (t_ob x) *)
(* | mcl_unit: maclane 1 1 *)
| mcl_id: forall a, maclane a a
| mcl_comp: forall a b c, maclane a b -> maclane b c -> maclane a c
| mcl_tensor: forall a b c d, maclane a b -> maclane c d -> maclane (a⊗c) (b⊗d)
| mcl_inv: forall a b, maclane a b -> maclane b a
| mcl_assoc: forall a b c, maclane ((a⊗b)⊗c) (a⊗(b⊗c))
| mcl_unitl: forall a, maclane (1⊗a) a
| mcl_unitr: forall a, maclane (a⊗1) a
.

Notation "f ∘ g" := (mcl_comp g f).
Notation "f · g" := (mcl_tensor f g).
Notation "f ⁻¹" := (mcl_inv f).

(* Fixpoint mcl_id {a}: maclane a a := *)
(*   match a with *)
(*   | t_ob x => mcl_var x *)
(*   | t_unit => mcl_unit *)
(*   | t_tensor a b => mcl_id · mcl_id *)
(*   end. *)

(** functoriality of [⊙] in its second argument *)
Fixpoint Norm12 a n m (h: maclane n m): maclane (a ⊙ n) (a ⊙ m) :=
  match a return maclane (a ⊙ n) (a ⊙ m) with
  | 1 => h
  | a ⊗ b => Norm12 a (Norm12 b h)
  | _ => mcl_id _ · h
  end.

(** functoriality of [Norm] in its first argument
    (the function J[|·|]_n in Peter and Ilya's paper,
     which we can define in one go)
 *)
Fixpoint Norm21 a b (f: maclane a b) n: maclane (a ⊙ n) (b ⊙ n) :=
  match f with
  | g ∘ f => Norm21 g n ∘ Norm21 f n
  | f · g => Norm12 _ (Norm21 g n)  ∘ Norm21 f _
  | f ⁻¹ => (Norm21 f n)⁻¹
  | _ => mcl_id _
  end.

(** alternative definition of [Norm21], via propositional equality,
    (like in Peter and Ilya's paper)  *)
Lemma Norm_eq a b (h: maclane a b): forall n, a⊙n = b⊙n.
Proof.
  induction h=>//=n.
  by rewrite IHh1.
  by rewrite IHh2.
Defined.

(** intuitively, [Norm21'] always returns the identity *)
Definition Norm21' a b (h: maclane a b) n: maclane (a ⊙ n) (b ⊙ n).
Proof. rewrite (Norm_eq h). exact: mcl_id. Defined.

(** normalising natural isomorphism *)
Fixpoint ξ a n: maclane (a ⊗ n) (a ⊙ n) :=
  match a with
  | t_ob x => mcl_id _
  | t_unit => mcl_unitl _
  | t_tensor a b => ξ _ _ ∘ mcl_id _ · ξ _ _ ∘ mcl_assoc _ _ _
  end.

(** final functor and normalising natural isomorphism
    ([Norm=Nf] and [φ=ν] in Peter and Ilya's paper) *)
Definition Nf a := a ⊙ nil.
Definition φ a: maclane a (Nf a) := ξ a nil ∘ (mcl_unitr a)⁻¹.

Theorem find_MacLane a b (e: Nf a = Nf b): maclane a b.
Proof.
  apply: mcl_comp. exact/φ.
  rewrite e. apply: mcl_inv. exact/φ. 
Qed.

(** canonization functor *)
Definition canonize a b (h: maclane a b): maclane a b :=
  mcl_inv (φ b) ∘ Norm21 h nil ∘ φ a.

(** additional properties *)

Lemma Norm_arity n m: n ⊙ m = n++m.
Proof. elim:n=>//=. congruence. Qed. 

Lemma Nf_arity n: Nf n = n.
Proof. by rewrite /Nf Norm_arity List.app_nil_r. Qed. 

(* need to be [Defined] for the normalisation procedure to compute *)
Lemma Norm_app a n m: a ⊙ (n++m) = (a⊙n) ++ m.
Proof. revert n. elim:a=>//= r IHr t IHt n. by rewrite IHt IHr. Defined.

Lemma Nf_tensor a b: Nf (a⊗b) = Nf a ++ Nf b.
Proof. by rewrite /Nf -Norm_app. Defined.

End t.
Arguments t_unit {_}.
Arguments mcl_id {_ _}, {_}.
Arguments n_id {_} _/.
Arguments n_tensor {_} _ _ _/.

(** evaluation of tensor-unit expressions *)
Fixpoint eval_tree {𝐂: PreMonoidalCat} (a: tree 𝐂): 𝐂 :=
  match a with
  | t_ob A => A
  | t_unit => unit 
  | t_tensor a b => eval_tree a ⊗ eval_tree b
  end.

(** tweaking coercions to use [eval_tree] from [tree] also to classes before [premonoidalcat.sort]
(i.e., cat, precat, quiver) *)
(* Coercion eval_tree: tree >-> premonoidalcat.sort. *)
Notation "t" := (eval_tree t) (only printing, at level 1).
Elpi Accumulate coercion.db lp:"
coercion _ V T E R :- coq.unify-eq T {{tree _}} ok, coq.unify-eq E {{quiver.sort _}} ok, !, R = {{eval_tree lp:V}}.
".

Definition eval_arity {𝐂: PreMonoidalCat} (n: arity 𝐂) := eval_tree (arity_tree n).

(** tweaking coercions to use [eval_arity] from [arity] also to classes before [premonoidalcat.sort]
(i.e., cat, precat, quiver) *)
(* Coercion eval_arity: arity >-> premonoidalcat.sort. *)
Notation "t" := (eval_arity t) (only printing, at level 1).
Elpi Accumulate coercion.db lp:"
coercion _ V T E R :- coq.unify-eq T {{arity _}} ok, coq.unify-eq E {{quiver.sort _}} ok, !, R = {{eval_arity lp:V}}.
".


Section s.

Context {𝐂: PreMonoidalCat}.
Implicit Types a b c d: tree 𝐂.  

(** evaluation of MacLane expressions *)
Fixpoint eval_maclane a b (h: maclane a b): a ~> b := 
  match h with
  | mcl_id => idmap
  | mcl_comp f g => eval_maclane g ∘ eval_maclane f
  | mcl_tensor f g => eval_maclane f · eval_maclane g
  | mcl_inv f => eval_maclane_inv f
  | mcl_assoc a b c => assoc a b c
  | mcl_unitl a => unitl a
  | mcl_unitr a => unitr a
  end
with eval_maclane_inv a b (h: maclane a b): b ~> a := 
  match h with
  | mcl_id => idmap
  | mcl_comp f g => eval_maclane_inv f ∘ eval_maclane_inv g
  | mcl_tensor f g => eval_maclane_inv f · eval_maclane_inv g
  | mcl_inv f => eval_maclane f
  | mcl_assoc a b c => assoc' a b c
  | mcl_unitl a => unitl' a
  | mcl_unitr a => unitr' a
  end.

Lemma mcl_isoK a b (h: maclane a b): eval_maclane h ∘ eval_maclane_inv h ≡ idmap
with mcl_isoK' a b (h: maclane a b): eval_maclane_inv h ∘ eval_maclane h ≡ idmap.
Proof.
  - destruct h=>//=.
    -- cat.
    -- by rewrite compoA -(compoA _ (eval_maclane h1)) mcl_isoK cats mcl_isoK.
    -- by rewrite exchange 2!mcl_isoK tensor_id.
    -- exact: isoK.
    -- exact: isoK.
    -- exact: isoK.
  - destruct h=>//=.
    -- cat.
    -- by rewrite compoA -(compoA _ (eval_maclane_inv h2)) mcl_isoK' cats mcl_isoK'.
    -- by rewrite exchange 2!mcl_isoK' tensor_id.
    -- exact: isoK'. 
    -- exact: isoK'.
    -- exact: isoK'.
Qed.

HB.instance Definition _ a b (h: maclane a b) :=
  @IsIso.Build _ _ _ (eval_maclane h) (eval_maclane_inv h) (mcl_isoK h) (mcl_isoK' h).
HB.instance Definition _ a b (h: maclane a b) :=
  @IsIso.Build _ _ _ (eval_maclane_inv h) (eval_maclane h) (mcl_isoK' h) (mcl_isoK h).

(* TOTHINK: remove? *)
Coercion eval_maclane: maclane >-> Setoid.sort.

Definition iso_maclane a b (h: maclane a b): a ≃ b := eval_maclane h. 

Lemma eval_maclane_invE a b (h: maclane a b): h⁻¹ = mcl_inv h.
Proof. done. Qed.

Lemma eval_maclane_cast a a' b b' (f: maclane a b) aa bb:
  eval_maclane (@cast2' _ _ a b a' b' f aa bb) =
    hcast' f (f_equal eval_tree aa) (f_equal eval_tree bb). 
Proof. by destruct aa; destruct bb. Qed.


End s.

Ltac reify_ob A :=
  lazymatch A with
  | @unit ?𝐂 => constr:(@t_unit 𝐂)
  | ?A ⊗ ?B =>
      let a := reify_ob A in
      let b := reify_ob B in
      constr:(t_tensor a b)
  | eval_tree ?t => constr:(t)
  | ?A => constr:(t_ob A)
  end.

Ltac find_maclane :=
  match goal with
  | |- Bridge ?A ?B => 
      let a := reify_ob A in
      let b := reify_ob B in
      refine (iso_maclane (@find_MacLane _ a b erefl))
  end.
Local Hint Extern 0 (Bridge _ _) => find_maclane: typeclass_instances.


Section test.
Context {𝐂: PreMonoidalCat}.
Variables A B C: 𝐂.
Variables a b c: tree 𝐂.
Variables h k l Γ Δ: arity 𝐂.
Check mcl: A⊗unit ~> A. 
Check mcl: (A⊗unit)⊗B ~> A⊗B⊗unit.
Check mcl: A⊗unit⊗B ~> A⊗B⊗unit.
Check mcl: unit ⊗ A ⊗ B ⊗ C ~> A ⊗ B ⊗ unit ⊗ C.
Check mcl: unit ⊗ h ⊗ B ⊗ k ~> h ⊗ B ⊗ unit ⊗ k.
Check mcl: unit ⊗ h ⊗ B ⊗ b ~> h ⊗ B ⊗ unit ⊗ b.

Goal (mcl: A⊗unit ~> A) ≡ (acast idmap: A⊗unit ~> A).
Abort.
Goal (mcl: A⊗unit ~> A) ∘ (acast idmap: unit⊗A ~> A⊗unit) ∘ (mcl: A ~> unit⊗A) ≡ idmap.
Abort.
Goal forall (f: A ~> A) (g: A⊗unit ~> A), g ∘∘ idmap ∘∘ f ≡ g ∘∘ f.
Abort.
Goal assoc A B C ≡ mcl.
Abort.
Goal forall (f: Γ ~> A) (g: Δ ~> B) (h: A⊗(unit⊗B) ~> C), h ∘∘ f · g ≡ h ∘∘ ((f · idmap) ∘ (idmap · g)).
Abort.
Fail Goal (mcl: Γ++Δ ~> Γ⊗Δ) ≡ acast (mcl: Γ++Δ ~> Γ⊗unit⊗Δ). (* solved later in gmaclane *)

Check A: A ~> A.
End test. 


(** ** MacLane coherence theorem  *)

Section s.
  
Context {𝐂: MonoidalCat}.
Implicit Types A B C D: 𝐂.
Implicit Types a b c d: tree 𝐂.
Implicit Types n m: arity 𝐂.
Notation "1" := t_unit.



Lemma pentagon_inv A B C D:
    idmap A · assoc' B C D \; assoc' A (B⊗C) D \; assoc' A B C · idmap D
      ≡ assoc' A B (C⊗D) \; assoc' (A⊗B) C D.
Proof. rewrite -compoA. apply/inv_inj. exact/pentagon. Qed.

Lemma triangle_alt A B:
    idmap A · unitl B
      ≡ unitr A · idmap B ∘ assoc' A unit B.
Proof. rewrite iso_src. exact/triangle. Qed.

(** Kelly'64 + MacLane 1971 second edition p165 exercise 1
   (careful: there, assoc = α⁻¹, unitl = λ, unitr = ρ) *)
Lemma triangle': forall A B,
    unitl (A⊗B) ∘ assoc unit A B
      ≡ unitl A · idmap B.
Proof.
  move=>C D.
  set A := unit. 
  suff: (idmap A · (unitl (C⊗D) ∘ assoc unit C D)
             ≡ idmap A · (unitl C · idmap D)).
  rewrite 2!tensorUl. by apply: (proj1 (cast_eqv_iff _ _)). 
  clearbody A.
  rewrite tensor_comp_r_src.

  rewrite triangle_alt. 
  apply: (mono (assoc' A C D)).
  change (  assoc' A C D ∘ (unitr A · idmap ∘ assoc' A unit (C ⊗ D) ∘ idmap · assoc unit C D)
  ≡ assoc' A C D ∘ idmap · unitl C · idmap).
  rewrite !compoA id_tensor 2!ntx_assoc'. 

  rewrite -2!compoA (compoA _ _ (assoc' _ _ _)) -pentagon_inv.
  rewrite -!compoA isoK'.
  rewrite !cats. apply: comp_eqv=>//.
  rewrite -triangle.
  rewrite tensor_comp_l_src.
  rewrite -compoA isoK'. cat. 
Qed.


(** we first prove that [Norm21=Norm21']
    (we could also have worked directly with [Norm21'])
 *)

Lemma Norm21'_comp a b c (f: maclane a b) (g: maclane b c) n:
  Norm21' (mcl_comp f g) n ≡ Norm21' g n ∘ Norm21' f n.
Proof.
  rewrite /Norm21'/=.
  case (Norm_eq g n); cbn. 
  case (Norm_eq f n); cbn.
  cat.
Qed.  

Lemma Norm21'_inv a b (f: maclane a b) n:
  Norm21' (mcl_inv f) n ≡ eval_maclane_inv (Norm21' f n).
Proof.
  rewrite /Norm21'/=.
  by case (Norm_eq f n).
Qed.  

Lemma Norm12_eqv a: forall n m (h k: maclane n m), h ≡ k -> Norm12 a h ≡ Norm12 a k.
Proof.
  induction a=>//=n m h k E.
  - exact: tensor_eqv. 
  - by apply IHa1, IHa2. 
Qed.

Lemma Norm12_id a: forall n, Norm12 a (mcl_id n) ≡ idmap.
Proof.
  induction a as [x| |a IHa c IHc]=>//=b.
  - exact: tensor_id.
  - rewrite -IHa. exact: Norm12_eqv. 
Qed.

Lemma Norm21'_tensor a b c d (f: maclane a b) (g: maclane c d) n:
  Norm21' (mcl_tensor f g) n ≡ Norm12 _ (Norm21' g _) ∘ Norm21' f _.
Proof.
  rewrite /Norm21'/=. 
  case (Norm_eq g n).
  rewrite Norm12_id; cbn. cat. 
Qed.

Lemma Norm21E a b (f: maclane a b): forall n, Norm21 f n ≡ Norm21' f n.
Proof.
  induction f=>//=n.
  - rewrite Norm21'_comp; exact/comp_eqv.
  - rewrite Norm21'_tensor. apply: comp_eqv=>//.  exact/Norm12_eqv.
  - rewrite Norm21'_inv. exact/inv_inj. 
Qed.

Lemma Norm_eq_unique a b (f g: maclane a b) n: Norm_eq f n = Norm_eq g n.
Proof. exact: UIP_ob_list. Qed.

(** by UIP, it follows that the morphism returned by [Norm21 f n] does not depend on [f] *)
Proposition Norm21_unique a b (f g: maclane a b) n: Norm21 f n ≡ Norm21 g n.
Proof. by rewrite 2!Norm21E/Norm21' (Norm_eq_unique f g). Qed.

(** naturality of [ξ] in its second argument *)
Lemma ntx_ξ2 a: forall n m (k: maclane n m),
    ξ a m  ∘  idmap · k ≡ Norm12 a k  ∘  ξ a n.
Proof.
  induction a as [x| |a IHa b IHb]=>n m k/=;
    rewrite -/eval_tree. (* TOFIX: /eval_tree *)
  - cbn. cat.
  - exact: ntx_unitl.
  - rewrite id_tensor -!compoA ntx_assoc.
    rewrite (compoA _ _ (_·_)) exchange IHb !cats.
    rewrite tensor_comp_r_tgt !compoA IHa. cat.
Qed.

(** naturality of [ξ] in its first argument *)
Lemma ntx_ξ1 a b (h: maclane a b):
  forall n, ξ b n  ∘  h · idmap ≡ Norm21 h n  ∘  ξ a n.
Proof.
  induction h as [a|a b c f IHf g IHg|a a' b b' f IHf g IHg|a b f IHf| | | ]=>/=n; simpl. 
    rewrite -/eval_tree.        (* TOFIX: /eval_tree *)
  - rewrite tensor_id. cat.
  - rewrite tensor_comp_l_tgt compoA IHg -compoA IHf. cat.
  - rewrite !compoA -(compoA _ _ (Norm12 _ _)) -IHf !compoA.
    rewrite -ntx_ξ2 -!compoA.
    rewrite (compoA (assoc _ _ _)) -tensor_rl.
    rewrite (compoA (assoc _ _ _)) exchange -IHg.
    rewrite -exchange -compoA -ntx_assoc. cat.
  - rewrite iso_tgt_r/= compoA -IHf -compoA exchange.
    rewrite (isoK f) cats tensor_id. cat.
  - rewrite cats.
    rewrite -tensor_id.
    rewrite -!compoA (compoA _ _ (assoc _ _ _)) ntx_assoc.
    rewrite tensor_comp_r_src tensor_comp_r_tgt.
    rewrite -!compoA -pentagon. cat. 
  - rewrite ntx_unitl -triangle'. cat.
  - rewrite -triangle. cat.
Qed.

(** naturality of [φ] *)
Lemma ntx_φ a b (h: maclane a b):
  φ b  ∘  h ≡ Norm21 h _ ∘  φ a.
Proof.
  rewrite /Norm/= compoA.
  rewrite -(ntx_ξ1 h nil) -!compoA. 
  by rewrite -ntx_unitr'.
Qed.

(** soundness of canonization *)
Proposition canonizeE a b (f: maclane a b): f ≡ canonize f.
Proof.
  rewrite /canonize/=.
  rewrite -compoA -ntx_φ compoA isoK'. cat.
Qed.

(** MacLane's coherence theorem follows *)
Theorem MacLane a b (f g: maclane a b): f ≡ g.
Proof.
  rewrite (canonizeE f) (canonizeE g) /=.
  repeat apply: comp_eqv=>//.
  exact/Norm21_unique. 
Qed.

End s.


(** preliminary [MacLane] tactic (superseded by the one defined in [monoidal_gmaclane])  *)

Ltac reify_mcl f :=
  lazymatch f with
  | idmap ?A =>
      let a := reify_ob A in
      constr:(@mcl_id _ a)
  | ?f \; ?g =>
      let u := reify_mcl f in
      let v := reify_mcl g in
      constr:(mcl_comp u v)
  | inv ?f =>
      let f := (eval simpl in (iso.sort f)) in
      let u := reify_mcl f in
      constr:(mcl_inv u)
  | iso.sort ?f =>
      let u := reify_mcl f in
      constr:(u)
  | ?f · ?g =>
      let u := reify_mcl f in
      let v := reify_mcl g in
      constr:(mcl_tensor u v)
  | assoc ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(mcl_assoc a b c)
  | assoc' ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(mcl_inv (mcl_assoc a b c))
  | unitl ?A =>
      let a := reify_ob A in
      constr:(mcl_unitl a)
  | unitl' ?A =>
      let a := reify_ob A in
      constr:(mcl_inv (mcl_unitl a))
  | unitr ?A =>
      let a := reify_ob A in
      constr:(mcl_unitr a)
  | unitr' ?A =>
      let a := reify_ob A in
      constr:(mcl_inv (mcl_unitr a))
  | mcl ?f => reify_mcl f
  | iso_maclane ?m => constr:(m)
  | eval_maclane ?m => constr:(m)
  | eval_maclane_inv ?m => constr:(mcl_inv m)
  end.


Ltac MacLane_debug :=
  lazymatch goal with
    |- ?f ≡ ?g =>
      let u := reify_mcl f in
      let v := reify_mcl g in
      move:(MacLane u v)
  end.

Ltac MacLane :=
  (try reflexivity);
  match goal with
  | |- comp _ _ ≡ comp _  _ => apply: comp_eqv; MacLane
  | |- bcomp _ _ _ ≡ bcomp _ _ _ => apply: bcomp_eqv; MacLane
  | |- tensor22 _ _ ≡ tensor22 _ _ => apply: tensor_eqv; MacLane
  | |- hcast _ ≡ hcast _ => apply: hcast_eqv'; MacLane
  | |- cast _ ≡ cast _ => apply: cast_eqv; MacLane
  | |- _ => by MacLane_debug
  end.

Section tests'.

Context {𝐂: MonoidalCat}.
Variables A B C D: 𝐂.
Variables h: arity 𝐂.

Goal A ≡ A.
Proof. MacLane. Qed.
Goal A·B ≡ A·B.
Proof. MacLane. Qed.
Goal unitl A \; unitl' A ≡ idmap.
Proof. MacLane. Qed.
Goal assoc A B C ≡ assoc A B C.
Proof. MacLane. Qed.
Goal A · assoc B C D ∘ assoc A (B⊗C) D ∘ assoc A B C · D
     ≡ assoc A B (C⊗D) ∘ assoc (A⊗B) C D.
Proof. MacLane. Qed.

Goal A · unitl B ∘ assoc A unit B ≡ unitr A · B.
Proof. MacLane. Qed.

Goal A · unitl (B⊗C) ∘ assoc A unit (B⊗C) ≡ unitr A · (B⊗C).
Proof. MacLane. Qed.

Goal A · unitl (B⊗C) ∘ assoc A unit (B⊗C) ≡ mcl.
Proof. MacLane. Qed.

Goal A · unitl h ∘ assoc A unit h ≡ unitr A · eval_arity h.
Proof. MacLane. Qed.

Goal unitl unit ≡[𝐂 _ _] unitr unit. 
Proof. MacLane. Qed.

Goal unitl' A ≡ inv (unitl A). 
Proof. MacLane. Qed.

Goal inv (unitl A ∘ idmap) ≡ mcl. 
Proof. MacLane. Qed.

End tests'.

