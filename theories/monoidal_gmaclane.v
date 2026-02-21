(** * inferrence of (generalised) MacLane isomorphisms,
      generalised MacLane's coherence theorem, and associated tactic *)

Require Import arity monoidal_def monoidal_maclane.
From elpi Require Import elpi coercion.

Local Open Scope cat_scope. 

Section s.
Context {X: Type}.

(** generalised tensor-tree expressions *)
Inductive gtree :=
| gt_ob(x: X)
| gt_tree(t: tree X)           (* remove? *)
| gt_unit
| gt_tensor(s t: gtree)
| gt_trees(h: gtrees)
with gtrees :=
| gt_ar(a: arity X)
| gt_nf(t: tree X)
| gt_gnf(t: gtree)
| gt_nil
| gt_cons(s: gtree)(h: gtrees)
| gt_app (h k: gtrees).

Fixpoint gNorm t: norm X :=
  match t with
  | gt_ob x => cons x
  | gt_tree t => Norm t
  | gt_unit => n_id
  | gt_tensor s t => n_tensor (gNorm s) (gNorm t)
  | gt_trees l => gNorm' l
  end
with gNorm' t: norm X :=
  match t with
  | gt_ar a => List.app a
  | gt_nf t => Norm t
  | gt_gnf t => gNorm t
  | gt_nil => n_id
  | gt_cons t q => n_tensor (gNorm t) (gNorm' q)
  | gt_app p q => n_tensor (gNorm' p) (gNorm' q)
  end.

Definition gNf a := gNorm a nil.
Definition gNf' t := gNorm' t nil.

(* gNf_tensor below should be [Defined] for the normalisation tactic to compute later on *)

Lemma gNorm_app (t: gtree) (n m: arity X): gNorm t (n ++ m) = gNorm t n ++ m
with gNorm'_app (t: gtrees) (n m: arity X): gNorm' t (n ++ m) = gNorm' t n ++ m.
Proof.
  destruct t=>//=. exact/Norm_app. by rewrite gNorm_app. 
  destruct t=>//=. exact/esym/aappA. exact/Norm_app. by rewrite gNorm'_app. by rewrite gNorm'_app. 
Defined.

Lemma gNf_tensor a b: gNf (gt_tensor a b) = gNf a ++ gNf b.
Proof. by rewrite /gNf -gNorm_app. Defined.

Fixpoint tensor_arity (l: arity X) (k: tree X): tree X :=
  match l with
  | nil => k
  | cons x q => t_tensor (t_ob x) (tensor_arity q k)
  end.

Lemma tensor_arity_app h k t: tensor_arity (h++k) t = tensor_arity h (tensor_arity k t).
Proof. elim: h=>//=. congruence. Defined.

Lemma Norm_tensor_arity a t b: Norm (tensor_arity a t) b = a ++ Norm t b.
Proof. elim:a=>//=. congruence. Qed.

Fixpoint tree_gtree t :=
  match t with
  | t_ob x => gt_ob x
  | t_unit => gt_unit
  | t_tensor s t => gt_tensor (tree_gtree s) (tree_gtree t)
  end.

End s.
Arguments gtree: clear implicits.
Arguments gtrees: clear implicits.

Section s.
Context {𝐂: PreMonoidalCat}.

Lemma eval_arityE (l: arity 𝐂): eval_arity l = eval_tree (tensor_arity l t_unit).
Proof. rewrite /eval_arity. elim: l=>//=. congruence. Defined.

Fixpoint eval_gtree a: 𝐂 :=
  match a with
  | gt_ob x => x
  | gt_tree t => t
  | gt_unit => unit
  | gt_tensor a b => eval_gtree a ⊗ eval_gtree b
  | gt_trees t => eval_arity (eval_gtrees t)
  end
with eval_gtrees t: arity 𝐂 :=
  match t with
  | gt_ar a => a
  | gt_nf t => Nf t
  | gt_gnf t => gNf t
  | gt_nil => nil
  | gt_cons a q => eval_gtree a :: eval_gtrees q
  | gt_app h k => eval_gtrees h ++ eval_gtrees k
  end.

Fixpoint gtree_tree (t: gtree 𝐂): tree 𝐂 :=
  match t with
  | gt_ob x => t_ob x
  | gt_tree t => t
  | gt_unit => t_unit
  | gt_tensor s t => t_tensor (gtree_tree s) (gtree_tree t)
  | gt_trees h => gtrees_tree h t_unit
  end
with gtrees_tree (t: gtrees 𝐂) k: tree 𝐂 :=
  match t with
  | gt_ar l => tensor_arity l k
  | gt_nf t => tensor_arity (Nf t) k
  | gt_gnf t => tensor_arity (gNf t) k
  | gt_nil => k
  | gt_cons s t => t_tensor (gtree_tree s) (gtrees_tree t k)
  | gt_app s t => gtrees_tree s (gtrees_tree t k)
  end.

Lemma eval_tree_gtree t: eval_tree t = eval_gtree (tree_gtree t).
Proof. elim:t=>//=. congruence. Qed.

Lemma gtree_tree_gtree t: gtree_tree (tree_gtree t) = t.
Proof. elim:t=>//=. congruence. Qed.

Fixpoint eval_gtree_tree t: eval_gtree t = eval_tree (gtree_tree t)
with eval_gtrees_tree l k k':
  eval_tree k = eval_tree k' ->
  eval_tree (tensor_arity (eval_gtrees l) k) = eval_tree (gtrees_tree l k').
Proof.
  - destruct t=>//=.
    by rewrite 2!eval_gtree_tree.
    rewrite eval_arityE. exact/(eval_gtrees_tree _ t_unit).
  - destruct l=>//=e.
    -- elim: a e=>//=a q IH /IH e. congruence.
    -- elim:(Nf t) e=>//=a q IH /IH e. congruence.
    -- elim:(gNf t) e=>//=a q IH /IH e. congruence.
    -- rewrite eval_gtree_tree. f_equal. exact/eval_gtrees_tree.
    -- rewrite tensor_arity_app. by do 2 apply eval_gtrees_tree.
Defined.

Lemma Norm_gtrees_tree l h k: Norm (gtrees_tree l h) k = Norm (gtrees_tree l t_unit) (Norm h k).
Proof.
  move: h k. elim: l=>//=.
  - move=>a h k. by rewrite 2!Norm_tensor_arity.
  - move=>a h k. by rewrite 2!Norm_tensor_arity.
  - move=>a h k. by rewrite 2!Norm_tensor_arity.
  - congruence.
  - move=>p IHp q IHq h k. by rewrite IHp IHq (IHp (gtrees_tree _ _)).
Qed.

Fixpoint gNormE t k: gNorm t k = Norm (gtree_tree t) k
with gNorm'E l k: gNorm' l k = Norm (gtrees_tree l t_unit) k.
Proof.
  - destruct t=>//=.
    by rewrite 2!gNormE. 
  - destruct l=>//=.
    by rewrite Norm_tensor_arity.
    rewrite Norm_tensor_arity/=. exact/(Norm_app t nil).
    rewrite Norm_tensor_arity/=. exact/(gNorm_app t nil).
    by rewrite gNormE gNorm'E.
    rewrite 2!gNorm'E. symmetry. exact/Norm_gtrees_tree. 
Qed.

Corollary gNfE t: gNf t = Nf (gtree_tree t).
Proof. exact/gNormE. Qed.

Definition gmaclane a b := maclane (gtree_tree a) (gtree_tree b).

Theorem find_gMacLane a b (e: gNf a = gNf b): gmaclane a b.
Proof.
  have{}e : Nf (gtree_tree a) = Nf (gtree_tree b) by rewrite -2!gNfE.
  exact: find_MacLane e. 
Qed.

Definition iso_gmaclane a b (h: gmaclane a b): eval_gtree a ≃ eval_gtree b :=
  locked (icast' (iso_maclane h) (esym (eval_gtree_tree a)) (esym (eval_gtree_tree b))).
Definition eval_gmaclane a b (h: gmaclane a b): eval_gtree a ~> eval_gtree b := iso_gmaclane h.

Lemma eval_gmaclaneE a b (h: gmaclane a b):
  iso.sort (iso_gmaclane h) = hcast' (eval_maclane h) (esym (eval_gtree_tree a)) (esym (eval_gtree_tree b)).
Proof. by rewrite /iso_gmaclane-lock -hcast_iso. Qed.

Coercion iso_gmaclane: gmaclane >-> iso.type.
Local Coercion gtree_tree: gtree >-> tree.

Definition gmcl_id a: gmaclane a a := mcl_id a. 
Definition gmcl_comp a b c (f: gmaclane a b) (g: gmaclane b c): gmaclane a c := mcl_comp f g. 
Definition gmcl_inv a b (f: gmaclane a b): gmaclane b a := mcl_inv f. 
Definition gmcl_tensor a b c d (f: gmaclane a b) (g: gmaclane c d): gmaclane (gt_tensor a c) (gt_tensor b d) := mcl_tensor f g. 
Definition gmcl_assoc a b c: gmaclane (gt_tensor (gt_tensor a b) c) (gt_tensor a (gt_tensor b c)) := mcl_assoc a b c. 
Definition gmcl_assoc' a b c := gmcl_inv (gmcl_assoc a b c). 
Definition gmcl_unitl a: gmaclane (gt_tensor gt_unit a) a := mcl_unitl a. 
Definition gmcl_unitl' a := gmcl_inv (gmcl_unitl a). 
Definition gmcl_unitr a: gmaclane (gt_tensor a gt_unit) a := mcl_unitr a. 
Definition gmcl_unitr' a := gmcl_inv (gmcl_unitr a). 

Definition gmcl_eq a b (e: gtree_tree a = gtree_tree b): gmaclane a b :=
  cast2' (T:=@maclane _) (mcl_id (gtree_tree a)) erefl e. 
Definition gmcl_comp' a b b' c (f: gmaclane a b) (e: gtree_tree b = gtree_tree b') (g: gmaclane b' c): gmaclane a c :=
  (gmcl_comp f (gmcl_comp (gmcl_eq e) g)).

Definition gmcl_maclane s t (f: maclane s t): gmaclane (tree_gtree s) (tree_gtree t) :=
  cast2' f (esym (gtree_tree_gtree s)) (esym (gtree_tree_gtree t)).

Lemma eval_gmaclane_id a: gmcl_id a ≡ idmap.
Proof. by rewrite eval_gmaclaneE hcast_id. Qed.
Lemma eval_gmaclane_comp a b c (f: gmaclane a b) (g: gmaclane b c): gmcl_comp f g ≡ f \; g.
Proof. by rewrite !eval_gmaclaneE hcast_comp. Qed.
Lemma eval_gmaclane_inv a b (f: gmaclane a b): gmcl_inv f ≡ f⁻¹.
Proof.
  rewrite eval_gmaclaneE -eval_maclane_invE/=.
  rewrite hcast_inv. apply: inv_inj=>/=.
  rewrite -hcast_iso. cbn. by rewrite eval_gmaclaneE. 
Qed.

Lemma eval_gmaclane_tensor a b c d (f: gmaclane a b) (g: gmaclane c d): gmcl_tensor f g ≡ f · g.
Proof. by rewrite !eval_gmaclaneE hcast_tensor/= 2!tensor11_eq_sym. Qed.
Lemma eval_gmaclane_assoc a b c: gmcl_assoc a b c ≡ assoc (eval_gtree a) (eval_gtree b) (eval_gtree c).
Proof. by rewrite !eval_gmaclaneE/= -!tensor11_eq_sym hcast_assoc. Qed.
Lemma eval_gmaclane_assoc' a b c: gmcl_assoc' a b c ≡ assoc' (eval_gtree a) (eval_gtree b) (eval_gtree c).
Proof. rewrite eval_gmaclane_inv. apply: inv_inj. exact/eval_gmaclane_assoc. Qed.
Lemma eval_gmaclane_unitl a: gmcl_unitl a ≡ unitl (eval_gtree a).
Proof. rewrite !eval_gmaclaneE/=. by destruct (eval_gtree_tree a). Qed.
Lemma eval_gmaclane_unitl' a: gmcl_unitl' a ≡ unitl' (eval_gtree a).
Proof. rewrite eval_gmaclane_inv. apply: inv_inj. exact/eval_gmaclane_unitl. Qed.
Lemma eval_gmaclane_unitr a: gmcl_unitr a ≡ unitr (eval_gtree a).
Proof. rewrite !eval_gmaclaneE/=. by destruct (eval_gtree_tree a). Qed.
Lemma eval_gmaclane_unitr' a: gmcl_unitr' a ≡ unitr' (eval_gtree a).
Proof. rewrite eval_gmaclane_inv. apply: inv_inj. exact/eval_gmaclane_unitr. Qed.

Lemma eval_gmaclane_cast a a' b b' (f: gmaclane a b) aa bb:
  iso_gmaclane (@cast2' _ _ a b a' b' f aa bb) =
    icast' f (f_equal eval_gtree aa) (f_equal eval_gtree bb). 
Proof. by destruct aa; destruct bb. Qed.



Definition mcl_eq a b (e: gtree_tree a = gtree_tree b): eval_gtree a ~> eval_gtree b :=
  hcast' idmap (esym (eval_gtree_tree _)) (etrans (f_equal eval_tree e) (esym (eval_gtree_tree _))).
Lemma eval_gmaclane_eq a b e:
  @gmcl_eq a b e ≡ mcl_eq e.
Proof. rewrite /gmcl_eq !eval_gmaclaneE. by rewrite eval_maclane_cast hcastI/=/mcl_eq etrans_id. Qed.

Lemma eval_gmaclane_comp' a b b' c (f: gmaclane a b) e (g: gmaclane b' c): gmcl_comp' f e g ≡ f \; mcl_eq e \; g.
Proof. by rewrite 2!eval_gmaclane_comp eval_gmaclane_eq. Qed.

Lemma eval_gmaclane_maclane s t (f: maclane s t): gmcl_maclane f ≡ hcast' (eval_maclane f) (eval_tree_gtree s) (eval_tree_gtree t).
Proof. rewrite !eval_gmaclaneE eval_maclane_cast hcastI. MacLane. Qed.

End s.

(** reification of generalised tensor tree expressions *)

Ltac reify_ob A :=
  lazymatch A with
  | @unit ?𝐂 => constr:(@gt_unit 𝐂)
  | ?A ⊗ ?B =>
      let a := reify_ob A in
      let b := reify_ob B in
      constr:(gt_tensor a b)
  | eval_tree ?t => constr:(gt_tree t) (* tree_gtree ? *)
  | eval_gtree ?t => constr:(t)
  | eval_arity ?L =>
      let l := reify_ar L in
      constr:(gt_trees l)
  | ?A => constr:(gt_ob A)
  end
with reify_ar L :=
  lazymatch L with
  | @nil ?𝐂 => constr:(@gt_nil 𝐂)
  | ?A :: ?L =>
      let a := reify_ob A in
      let l := reify_ar L in
      constr:(gt_cons a l)
  | ?H ++ ?K =>
      let h := reify_ar H in
      let k := reify_ar K in
      constr:(gt_app h k)
  | Nf ?t =>
      constr:(gt_nf t)
  | gNf ?t =>
      constr:(gt_gnf t)
  | ?L => constr:(gt_ar L)
  end.

(** final tactic for inferring MacLane isomorphisms *)
Ltac find_gmaclane' :=
  unfold Bridge;
  match goal with
  | |- ?A ≃ ?B => 
      let a := reify_ob A in
      let b := reify_ob B in
      refine (iso_gmaclane (@find_gMacLane _ a b _))
  | |- ?A ~> ?B => 
      let a := reify_ob A in
      let b := reify_ob B in
      refine (eval_gmaclane (@find_gMacLane _ a b _))
  end.

Ltac find_gmaclane := by find_gmaclane'.
#[export] Hint Extern 0 (Bridge _ _) => find_gmaclane: typeclass_instances.

Section test_find_gmaclane.
Context {𝐂: PreMonoidalCat}.
Variables A B C: 𝐂.
Variables a b c: tree 𝐂.
Variables g: gtree 𝐂.
Variables h k l Γ Δ: arity 𝐂.
Check mcl: h⊗unit ~> h. 
Check mcl: (h++k)⊗B ~> h⊗k⊗B⊗unit.
Check mcl: h++A⊗unit⊗B::k ~> h⊗A⊗B⊗k.
Check (mcl: Γ++Δ ~> Γ⊗Δ) ≡ acast (mcl: Γ++Δ ~> Γ⊗unit⊗Δ).
Check mcl: unit ⊗ Nf b ⊗ C ~> b ⊗ C.
Check mcl: unit ⊗ gNf g ⊗ C ~> eval_gtree g ⊗ C.
Check mcl: unit ⊗ gNf (gt_tensor g g) ⊗ C ~> eval_gtree g ⊗ eval_gtree g ⊗ C. 
Check mcl: unit ⊗ Nf (t_tensor b c) ⊗ C ~> b ⊗ c ⊗ C.
Check mcl: unit ⊗ Nf (t_tensor b c) ⊗ C ~> b ⊗ Nf c ⊗ C.
Check mcl: unit ⊗ (h++k) ⊗ B ⊗ C ~> h ⊗ unit ⊗ k ⊗ B ⊗ unit ⊗ C.
Check mcl: A ⊗ (h++B::k) ⊗ C ~> A⊗ h ⊗ B ⊗ k ⊗ unit ⊗ C.
Check mcl: A ⊗ (h++(B⊗C)::k) ⊗ C ~> A⊗ h ⊗ B ⊗ C ⊗ k ⊗ unit ⊗ C.
Check mcl: A ⊗ (h++(B⊗l)::k) ⊗ C ~> A⊗ h ⊗ B ⊗ l ⊗ k ⊗ unit ⊗ C.

Check fun (f: A ~> (B⊗unit)) (g g': unit⊗B ~> A) => g ∘∘ f.
Check fun (f: A ~> (B⊗unit)) (g: unit⊗B ~> A) => acast g ∘ f.
Check fun (f: A ~> (B⊗unit)) (g: unit⊗B ~> A) => idmap ∘ g ∘∘ f.
Check fun (f: A ~> (B⊗unit)) (g: unit⊗B ~> A) => g ∘ acast f.
Check fun (f: A ~> (B⊗unit)) (g: B ~> A) => g ∘ mcl ∘ f.
End test_find_gmaclane.

(** generalised coherence theorem  *)
Theorem gMacLane {𝐂: MonoidalCat} {a b: gtree 𝐂} (f g: gmaclane a b): f ≡ g.
Proof. rewrite !eval_gmaclaneE. apply: hcast_eqv. exact/MacLane. Qed.

(** MacLane (iso)morphisms *)

HB.mixin Record isMacLane (𝐂: PreMonoidalCat) (A B: 𝐂) (f: A ~> B) := {
    #[canonical=no] src_gtree: gtree 𝐂; 
    #[canonical=no] tgt_gtree: gtree 𝐂; 
    #[canonical=no] srcE: eval_gtree src_gtree = A; 
    #[canonical=no] tgtE: eval_gtree tgt_gtree = B; 
    #[canonical=no] rmcl: gmaclane src_gtree tgt_gtree; 
    #[canonical=no] rmorE: f ≡ hcast' (iso_gmaclane rmcl) srcE tgtE;
  }.
HB.builders Context 𝐂 a b f of isMacLane 𝐂 a b f.
  Definition f': b ~> a := hcast' (rmcl⁻¹) tgtE srcE.
  Program Definition _iso := @IsIso.Build 𝐂 _ _ f f' _ _.
  Next Obligation. by rewrite rmorE/f' hcast_comp isoK hcast_id. Qed.
  Next Obligation. by rewrite rmorE/f' hcast_comp isoK' hcast_id. Qed.
  HB.instance Definition _ := _iso.
HB.end.

#[short(type="maclane")]
HB.structure Definition Maclane (𝐂: PreMonoidalCat) A B :=
  { f of isMacLane 𝐂 A B f }.
Arguments src_gtree {_ _ _}.
Arguments tgt_gtree {_ _ _}.
Arguments rmcl {_ _ _}.

Definition src_tree {𝐂: PreMonoidalCat} (A B: 𝐂) (f: maclane A B) := gtree_tree (src_gtree f).
Definition tgt_tree {𝐂: PreMonoidalCat} (A B: 𝐂) (f: maclane A B) := gtree_tree (tgt_gtree f).

Definition compatible {𝐂: PreMonoidalCat} {A B: 𝐂} (f g: maclane A B) :=
  src_tree f = src_tree g /\ tgt_tree f = tgt_tree g.
  
Lemma MacLane_cs {𝐂: MonoidalCat} {A B: 𝐂} (f g: maclane A B):
  compatible f g -> f ≡ g.
Proof.
  move=>[e e']. rewrite 2!rmorE.
  set rf := rmcl f. 
  set rg := rmcl g.
  unfold gmaclane in *. 
  have: eval_maclane (cast2' rf e e') ≡ eval_maclane rg by exact/MacLane.
  rewrite eval_maclane_cast !eval_gmaclaneE 2!hcastI.
  move=><-. rewrite hcastI. MacLane.
Qed.
Arguments MacLane_cs {_ _ _} _ _ & _. 


(** tweaking coercions to use [eval_gtree] from [gtree] also to classes before [premonoidalcat.sort]
(i.e., cat, precat, quiver) *)
(* Coercion eval_gtree: reified_ob >-> premonoidalcat.sort. *)
Notation "a" := (eval_gtree a) (only printing, at level 1).
Elpi Accumulate coercion.db lp:"
coercion _ V T E R :- coq.unify-eq T {{gtree _}} ok, coq.unify-eq E {{quiver.sort _}} ok, !, R = {{eval_gtree lp:V}}.
".


Section s.
Context {𝐂: PreMonoidalCat}.  
Implicit Types A B C D: 𝐂.  
Implicit Types a b c d: gtree 𝐂.  

Program Definition _mcl_id a :=
  @isMacLane.Build 𝐂 a a idmap
    a a erefl erefl
    (gmcl_id _) _. 
Next Obligation. intro a=>/=. by rewrite eval_gmaclane_id. Qed.
HB.instance Definition _ a := @_mcl_id a.
Definition maclane_id a: maclane a a := idmap. 

Lemma hcast_comp_src A B B' C A' B'' C' (f: A ~> B) (g: B' ~> C) 
  (a: A=A') (b: B=B'') (b': B'=B'') (c: C=C'):
  hcast' f a b \; hcast' g b' c = hcast' (hcast' f erefl (etrans b (esym b')) \; g) a c.
Proof. by destruct a; destruct b; destruct b'; destruct c. Qed.

Lemma hcast_comp_tgt A B B' C A' B'' C' (f: A ~> B) (g: B' ~> C) 
  (a: A=A') (b: B=B'') (b': B'=B'') (c: C=C'):
  hcast' f a b \; hcast' g b' c = hcast' (f \; hcast' g (etrans b' (esym b)) erefl) a c.
Proof. by destruct a; destruct b; destruct b'; destruct c. Qed.

Lemma hcast_gtree_src a' a B (e: gtree_tree a' = gtree_tree a) (e': eval_gtree a = eval_gtree a') (f: a ~> B): hcast' f e' erefl ≡ f ∘ mcl_eq e.
Proof.
  rewrite /mcl_eq. destruct (esym _), (etrans _ _). 
  rewrite (UIP_ob e' erefl)/=. cat.
Qed.

Lemma hcast_gtree_tgt A b b' (e: gtree_tree b = gtree_tree b') (e': eval_gtree b = eval_gtree b') (f: A ~> b): hcast' f erefl e' ≡ mcl_eq e ∘ f.
Proof.
  rewrite /mcl_eq. destruct (esym _), (etrans _ _). 
  rewrite (UIP_ob e' erefl)/=. cat.
Qed.  

Program Definition _mcl_comp A B C (f: maclane A B) (g: maclane B C)
  (e: tgt_tree f = src_tree g)
  :=
  @isMacLane.Build 𝐂 A C (g ∘ f)
    (src_gtree f) (tgt_gtree g) srcE tgtE
    (gmcl_comp' (rmcl f) e (rmcl g))
    _.
Next Obligation. 
  intros A B C f g e.
  rewrite 2!rmorE eval_gmaclane_comp'.
  by rewrite hcast_comp_tgt -hcast_gtree_src. 
Qed.
HB.instance Definition _ A B C f g e := @_mcl_comp A B C f g e.
#[refine] Definition maclane_comp A B C (f: maclane A B) (g: maclane B C) (e: tgt_tree f = src_tree g):
  maclane A C := f \; g.
Proof. done. Defined.

Program Definition _mcl_tensor A B C D (f: maclane A B) (g: maclane C D) :=
  @isMacLane.Build _ _ _ (f·g)
    (gt_tensor (src_gtree f) (src_gtree g))
    (gt_tensor (tgt_gtree f) (tgt_gtree g))
    (tensor11_eq srcE srcE)
    (tensor11_eq tgtE tgtE)
    (gmcl_tensor (rmcl f) (rmcl g)) _.
Next Obligation.
  intros a b c d f g. rewrite 2!rmorE.
  rewrite hcast_tensor eval_gmaclane_tensor. MacLane. 
Qed.
HB.instance Definition _ A B C D f g := @_mcl_tensor A B C D f g.
Definition maclane_tensor A B C D (f: maclane A B) (g: maclane C D):
  maclane _ _ := f · g.

Program Definition _mcl_inv A B (f: maclane A B) :=
  @isMacLane.Build _ _ _ (f⁻¹)
    (tgt_gtree f) (src_gtree f) tgtE srcE
    (gmcl_inv (rmcl f)) _.
Next Obligation.
  intros a b f.
  rewrite eval_gmaclane_inv hcast_inv. apply/inv_eqv.
  move: (@rmorE _ _ _ f). by rewrite hcast_iso. 
Qed.
HB.instance Definition _ A B f := @_mcl_inv A B f.
Definition maclane_inv A B (f: maclane A B):
  maclane _ _ := inv f.

Program Definition _mcl_assoc a b c :=
  @isMacLane.Build _ ((a ⊗ b) ⊗ c) (a ⊗ b ⊗ c) (assoc a b c)
    (gt_tensor (gt_tensor a b) c) (gt_tensor a (gt_tensor b c)) _ _ 
    (gmcl_assoc a b c) _.
Next Obligation. intros=>//=; by rewrite 3!roE. Qed.
Next Obligation. intros=>//=; by rewrite 3!roE. Qed.
Next Obligation. intros. rewrite eval_gmaclane_assoc hcast_assoc_//; apply: roE. Qed.
HB.instance Definition _ a b c := @_mcl_assoc a b c.
HB.instance Definition _ a b c := Maclane.on (assoc' a b c).
Definition maclane_assoc a b c: maclane _ _ := assoc a b c.
Definition maclane_assoc' a b c: maclane _ _ := assoc' a b c.

Program Definition _mcl_unitl a :=
  @isMacLane.Build _ _ _ (unitl a)
    (gt_tensor gt_unit a) a _ _ 
    (gmcl_unitl _) _.
Next Obligation. intros=>//=; by rewrite roE. Qed.
Next Obligation. intros=>//=; by rewrite roE. Qed.
Next Obligation. intros. by rewrite eval_gmaclane_unitl hcast_unitl_. Qed.
HB.instance Definition _ a := @_mcl_unitl a.
HB.instance Definition _ a := Maclane.on (unitl' a).
Definition maclane_unitl a: maclane _ _ := unitl a.
Definition maclane_unitl' a: maclane _ _ := unitl' a.

Program Definition _mcl_unitr a :=
  @isMacLane.Build _ _ _ (unitr a)
    (gt_tensor a gt_unit) a _ _
    (gmcl_unitr _) _.
Next Obligation. intros=>//=; by rewrite roE. Qed.
Next Obligation. intros=>//=; by rewrite roE. Qed.
Next Obligation. intros. by rewrite eval_gmaclane_unitr hcast_unitr_. Qed.
HB.instance Definition _ a := @_mcl_unitr a.
HB.instance Definition _ a := Maclane.on (unitr' a).
Definition maclane_unitr a: maclane _ _ := unitr a.
Definition maclane_unitr' a: maclane _ _ := unitr' a.

Program Definition _mcl_bcomp A B B' C (f: maclane A B) (m: maclane B B') (g: maclane B' C) 
  (i: tgt_tree f = src_tree m)
  (j: tgt_tree m = src_tree g)
  :=
  @isMacLane.Build 𝐂 A C (bcomp f g m)
    (src_gtree f) (tgt_gtree g) srcE tgtE
    (gmcl_comp' (rmcl f) i (gmcl_comp' (rmcl m) j (rmcl g))) _.
Next Obligation.
  intros a b b' c f m g i j. rewrite /bcomp-lock/=.
  rewrite 3!rmorE 2!eval_gmaclane_comp'.
  by rewrite 2!hcast_comp_tgt -2!hcast_gtree_src.
Qed.
HB.instance Definition _ A B B' C f g m i j := @_mcl_bcomp A B B' C f g m i j.
#[refine] Definition maclane_bcomp A B B' C (f: maclane A B) (m: maclane B B') (g: maclane B' C)
  (i: tgt_tree f = src_tree m)
  (j: tgt_tree m = src_tree g):
  maclane A C := bcomp f g m.
Proof. all: done. Defined.

Program Definition _mcl_cast A B B' C (f: maclane A B) (m: maclane B B') (g: maclane B' C) 
  (i: tgt_tree f = src_tree m)
  (j: tgt_tree m = src_tree g)
  :=
  @isMacLane.Build 𝐂 A C (cast' f g m)
    (src_gtree f) (tgt_gtree g) srcE tgtE
    (gmcl_comp' (rmcl f) i (gmcl_comp' (rmcl m) j (rmcl g))) _.
Next Obligation.
  intros a b b' c f m g i j. rewrite /cast-lock/=.
  rewrite 3!rmorE 2!eval_gmaclane_comp'.
  by rewrite 2!hcast_comp_tgt -2!hcast_gtree_src.
Qed.
HB.instance Definition _ A B B' C f g m i j := @_mcl_cast A B B' C f g m i j.
#[refine] Definition maclane_cast A B B' C (f: maclane A B) (m: maclane B B') (g: maclane B' C)
  (i: tgt_tree f = src_tree m)
  (j: tgt_tree m = src_tree g):
  maclane A C := cast' f g m.
Proof. all: done. Defined.

Program Definition _mcl_eval_gmaclane (s t: gtree 𝐂) (h: gmaclane s t)
  := @isMacLane.Build _ (eval_gtree s) (eval_gtree t) (eval_gmaclane h)
       s t erefl erefl
       h _.
Next Obligation. intros. by rewrite hcastK. Qed.
HB.instance Definition _ s t h := @_mcl_eval_gmaclane s t h.
Definition maclane_eval_gmaclane s t (h: gmaclane s t): maclane _ _ := eval_gmaclane h.

Program Definition _mcl_eval_maclane (s t: tree 𝐂) (h: monoidal_maclane.maclane s t)
  := @isMacLane.Build _ (eval_tree s) (eval_tree t) (eval_maclane h)
       (tree_gtree s) (tree_gtree t) (esym (eval_tree_gtree s)) (esym (eval_tree_gtree t))
       (gmcl_maclane h) _.
Next Obligation. intros. by rewrite eval_gmaclane_maclane hcastI hcastK. Qed.
HB.instance Definition _ s t h := @_mcl_eval_maclane s t h.
Definition maclane_eval_maclane s t (h: monoidal_maclane.maclane s t): maclane _ _ := eval_maclane h.

End s.
Arguments maclane_comp {_ _ _ _} _ _&.
Arguments maclane_bcomp {_ _ _ _ _} _ _ _&.
Arguments maclane_cast {_ _ _ _ _} _ _ _&.

Ltac reify_gmcl f :=
  lazymatch f with
  | idmap ?A =>
      let a := reify_ob A in
      constr:(maclane_id a)
  | ?f \; ?g =>
      let u := reify_gmcl f in
      let v := reify_gmcl g in
      uconstr:(maclane_comp u v _)
  | inv ?f =>
      let f := (eval simpl in (iso.sort f)) in
      let u := reify_gmcl f in
      uconstr:(maclane_inv u)
  | ?f · ?g =>
      let u := reify_gmcl f in
      let v := reify_gmcl g in
      uconstr:(maclane_tensor u v)
  | assoc ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(maclane_assoc a b c)
  | assoc' ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(maclane_assoc' a b c)
  | unitl ?A =>
      let a := reify_ob A in
      constr:(maclane_unitl a)
  | unitl' ?A =>
      let a := reify_ob A in
      constr:(maclane_unitl' a)
  | unitr ?A =>
      let a := reify_ob A in
      constr:(maclane_unitr a)
  | unitr' ?A =>
      let a := reify_ob A in
      constr:(maclane_unitr' a)
  | bcomp ?f ?g ?m =>
      let u := reify_gmcl f in
      let v := reify_gmcl g in
      let w := reify_gmcl m in
      uconstr:(maclane_bcomp u w v _ _)
  | cast' ?f ?g ?m =>
      let u := reify_gmcl f in
      let v := reify_gmcl g in
      let w := reify_gmcl m in
      uconstr:(maclane_cast u w v _ _)
  | blocked_id ?A =>
      let a := reify_ob A in
      constr:(maclane_id a)
  | blocked_comp ?f ?g =>
      let u := reify_gmcl f in
      let v := reify_gmcl g in
      uconstr:(maclane_comp u v _)
  | blocked_inv ?f =>
      let f := (eval simpl in (iso.sort f)) in
      let u := reify_gmcl f in
      uconstr:(maclane_inv u)
  | blocked_tens ?f ?g =>
      let u := reify_gmcl f in
      let v := reify_gmcl g in
      uconstr:(maclane_tensor u v)
  | @blocked_assoc _ ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(maclane_assoc a b c)
  | @blocked_assoc' _ ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(maclane_assoc' a b c)
  | @blocked_unitl _ ?A =>
      let a := reify_ob A in
      constr:(maclane_unitl a)
  | @blocked_unitl' _ ?A =>
      let a := reify_ob A in
      constr:(maclane_unitl' a)
  | @blocked_unitr _ ?A =>
      let a := reify_ob A in
      constr:(maclane_unitr a)
  | @blocked_unitr' _ ?A =>
      let a := reify_ob A in
      constr:(maclane_unitr' a)
  | iso.sort ?f => reify_gmcl f
  | reverse_coercion ?f _ => reify_gmcl f
  | mcl ?f => reify_gmcl f
  | iso_gmaclane ?m => constr:(maclane_eval_gmaclane m)
  | eval_gmaclane ?m => constr:(maclane_eval_gmaclane m)
  | eval_maclane ?m => constr:(maclane_eval_maclane m)
  | Maclane.sort ?m => constr:(m)
  | _ => fail "could not reify" f "as a MacLane morphism" 
  end.

Ltac gMacLane_gen tac :=
  unfold auto_eqv; 
  let rec gMacLane := 
    try reflexivity;
    rewrite /=;
    match goal with
    | |- comp _ _ ≡ comp _ _ => apply: comp_eqv; gMacLane
    | |- bcomp _ _ _ ≡ bcomp _ _ _ => apply: bcomp_eqv; gMacLane
    | |- tensor22 _ _ ≡ tensor22 _ _ => apply: tensor_eqv; gMacLane
    | |- hcast _ ≡ hcast _ => apply: hcast_eqv'; gMacLane
    | |- cast _ ≡ cast _ => apply: cast_eqv; gMacLane
    | |- ?f ≡ ?g =>
        let u := reify_gmcl f in
        let v := reify_gmcl g in
        tac u v
    end
  in gMacLane.
Ltac gMacLane_try_ u v :=
  unshelve refine (MacLane_cs u v _)=>//=;
    (try split); rewrite /=?tensor_arity_app//=.
Ltac gMacLane_solve u v := by gMacLane_try_ u v.
Ltac gMacLane_pose_ u v := epose (MacLane_cs u v _)=>//=.
Ltac gMacLane := gMacLane_gen gMacLane_solve.
Ltac gMacLane_try := gMacLane_gen gMacLane_try_.
Ltac gMacLane_pose := gMacLane_gen gMacLane_pose_.

#[export] Hint Extern 0 (auto_eqv _ _) => gMacLane: typeclass_instances.

Arguments eval_maclane: simpl never.
Arguments iso_gmaclane: simpl never.
Arguments eval_gmaclane: simpl never.

Section tests_gMacLane.
  
Context {𝐂: MonoidalCat}.
Variables A B C D: 𝐂.
Variables a b c d: tree 𝐂.
Variables h k l Γ Δ: arity 𝐂.

Goal A ≡ A.
Proof. gMacLane. Qed.
Goal A·B ≡ A·B.
Proof. gMacLane. Qed.
Goal unitl A \; unitl' A ≡ idmap.
Proof. gMacLane. Qed.
Goal assoc A B C ≡ assoc A B C.
Proof. gMacLane. Qed.
Goal A · assoc B C D ∘ assoc A (B⊗C) D ∘ assoc A B C · D
     ≡ assoc A B (C⊗D) ∘ assoc (A⊗B) C D.
Proof. gMacLane. Qed.

Goal A · unitl B ∘ assoc A unit B ≡ unitr A · B.
Proof. gMacLane. Qed.

Goal A · unitl (B⊗C) ∘ assoc A unit (B⊗C) ≡ unitr A · (B⊗C).
Proof. gMacLane. Qed.

Goal A · unitl (B⊗C) ∘ assoc A unit (B⊗C) ≡ mcl.
Proof. gMacLane. Qed.

Goal idmap h ≡ mcl.
Proof. gMacLane. Qed.

Goal idmap h ≡ mcl ∘ idmap.
Proof. gMacLane. Qed.

Goal A · unitl h ∘ assoc A unit h ≡ unitr A · eval_arity h.
Proof. gMacLane. Qed.

Goal acast (A · unitl h) ≡ unitr A · eval_arity h.
Proof. gMacLane. Qed.

Goal assoc A B C ∘∘ assoc A B C ≡ mcl.
Proof. gMacLane. Qed.

Goal unitl unit ≡[𝐂 _ _] unitr unit. 
Proof. gMacLane. Qed.

Goal unitl A ≡ inv (unitl' A). 
Proof. gMacLane. Qed.

Goal inv (unitl (A⊗B)) ≡ mcl. 
Proof. gMacLane. Qed.

Goal forall (s t: gtree 𝐂) (i: maclane s t), i ∘ inv i ≡ idmap. 
Proof. intros. gMacLane_try. unfold compatible. cbn. Abort.

(* Notation test_maclane f := (f ≡ idmap ∘ f) (only parsing). *)
Notation test_maclane f := (f ∘ inv f ≡ idmap) (only parsing).

Goal test_maclane (mcl: h⊗unit ≃ h).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: h⊗unit ~> h).
Proof. gMacLane. Qed.
  
Goal test_maclane (mcl: (h++k)⊗B ~> h⊗k⊗B⊗unit).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: h++A⊗unit⊗B::k ~> h⊗A⊗B⊗k).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: unit ⊗ Nf b ⊗ C ~> b ⊗ C).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: unit ⊗ Nf (t_tensor b c) ⊗ C ~> b ⊗ c ⊗ C).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: unit ⊗ Nf (t_tensor b c) ⊗ C ~> b ⊗ Nf c ⊗ C).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: unit ⊗ (h++k) ⊗ B ⊗ C ~> h ⊗ unit ⊗ k ⊗ B ⊗ unit ⊗ C).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: A ⊗ (h++B::k) ⊗ C ~> A⊗ h ⊗ B ⊗ k ⊗ unit ⊗ C).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: A ⊗ (h++(B⊗C)::k) ⊗ C ~> A⊗ h ⊗ B ⊗ C ⊗ k ⊗ unit ⊗ C).
Proof. gMacLane. Qed.

Goal test_maclane (mcl: A ⊗ (h++(B⊗l)::k) ⊗ C ~> A⊗ h ⊗ B ⊗ l ⊗ k ⊗ unit ⊗ C).
Proof. gMacLane. Qed.

End tests_gMacLane.

