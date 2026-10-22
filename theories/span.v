(** * spans *)

Require Import cat morphisms shape functor adjunction limit.

Local Open Scope cat_scope.

(** ** spans *)

#[primitive] HB.mixin Record IsSpan (𝐂: BareQuiver) (a b: ob 𝐂) (x: ob 𝐂) := {
    #[canonical=no] pi1: x ~> a;
    #[canonical=no] pi2: x ~> b;
  }.
#[short(type=Span)]
HB.structure Definition SPAN 𝐂 a b := {x of IsSpan 𝐂 a b x}. 

Section s.
Context {𝐂: BareQuiver} (a b: ob 𝐂).

Definition span (x: ob 𝐂) (f: x ~> a) (g: x ~> b) := x.
HB.instance Definition _ x f g := IsSpan.Build 𝐂 a b (@span x f g) f g.
Definition span_ (x: ob 𝐂) (f: x ~> a) (g: x ~> b): Span a b := span f g.

(** reversing a span *)
Definition spanC (x: Span a b): ob 𝐂 := x.
HB.instance Definition _ x := IsSpan.Build 𝐂 b a (spanC x) pi2 pi1.

End s.

(** ** span homomorphisms *)

Section s.
Context {𝐂: PreCat}.
Implicit Types a b: ob 𝐂.

Definition spanhom a b (x y: ob 𝐂) (x1: x ~> a) (x2: x ~> b) (y1: y ~> a) (y2: y ~> b) (f: x ~> y) :=
  f \; y1 ≡ x1 ∧ f \; y2 ≡ x2.
Definition Spanhom {a b} (x y: Span a b) := sig (fun f: x ~> y => spanhom pi1 pi2 pi1 pi2 f).
Coercion Spanhom_sort a b x y (f: @Spanhom a b x y): x ~> y := sval f.
Definition SpanH a b x y (f: @Spanhom a b x y): f \; pi1 ≡ pi1 ∧ f \; pi2 ≡ pi2 := proj2_sig f.
HB.instance Definition _ a b := IsQuiver.Build (Span a b) Spanhom.

Definition span_homC a b (x y: Span a b) (f: Spanhom x y): Spanhom (spanC x) (spanC y).
Proof. exists f. apply: swap_pair. exact: (SpanH f). Defined.
Definition span_homC' a b (x y: Span b a) (f: Spanhom (spanC x) (spanC y)): Spanhom x y.
Proof. exact: (span_homC f). Defined.
Definition span_homC1 a b (x: Span b a) (y: Span a b) (f: Spanhom (spanC x) y): Spanhom x (spanC y).
Proof. exact: (span_homC f). Defined.
Definition span_homC2 a b (x: Span a b) (y: Span b a) (f: Spanhom x (spanC y)): Spanhom (spanC x) y.
Proof. exact: (span_homC f). Defined.

End s.
Arguments spanhom {_} [_ _ _ _] _ _ _ _ _/.

(** ** the category of spans *)

Section s.
Context {𝐂: Cat} (a b: ob 𝐂).

Program Definition Span_id (x: Span a b): x ~> x := @exist _ _ idmap _.
Next Obligation. intro; split; exact: comp1o. Qed.

Program Definition Span_comp (x y z: Span a b) (f: x ~> y) (g: y ~> z): x ~> z :=
@exist _ _ (f \; g) _.
Next Obligation. intros; split; by rewrite compoA 2!SpanH. Qed.
HB.instance Definition _ := IsPreCat.Build (Span a b) Span_id Span_comp. 

Definition Span_sort := @SPAN.sort _ a b.
HB.instance Definition _ :=
  @IsFunctor.Build _ _ Span_sort (@Spanhom_sort _ a b) _ (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl). 
HB.instance Definition _ :=
  @IsFaithful.Build _ _ Span_sort (fun _ _ _ _ H => H).
HB.instance Definition _ :=
  FaithfulSubCat.Build _ (Span a b) Span_sort.
                  
(* Lemma _span_cat: IsCat (Span a b). *)
(* Proof. *)
(*   split=>*. *)
(*   - exact: comp1o.  *)
(*   - exact: compo1.  *)
(*   - exact: compoA.  *)
(*   - intros??????; exact: comp_eqv. *)
(* Qed. *)
(* HB.instance Definition _ := _span_cat.  *)

Definition Spaniso_sort (x y: Span a b) (i: x ≃ y): x ≃_𝐂 y :=
  iso_ (Spanhom_sort i¹) (Spanhom_sort i⁻¹) (invKl i) (invKr i). 

Lemma spanhom_inv (x y: Span a b) (i: x ≃_𝐂 y) (H: spanhom pi1 pi2 pi1 pi2 i¹):
  spanhom pi1 pi2 pi1 pi2 i⁻¹.
Proof. by split; rewrite iso_src H. Qed.

Definition spaniso_ (x y: Span a b) (i: x ≃_𝐂 y) (H: spanhom pi1 pi2 pi1 pi2 i¹): x ≃ y :=
  @iso_ _ x y (exist _ i¹ H) (exist _ i⁻¹ (spanhom_inv H)) (invKl i) (invKr i).

(** ** representation of spans as cones over the appropriate shape *)

Abbreviation Shape := (Diagram (shape.discrete bool) 𝐂).
Definition shape: Shape.
  exists (fun c => if c then a else b).
  done.
Defined.
Abbreviation Cone := (cone shape).

Definition Span_Cone (x: Span a b): Cone.
  exists (Span_sort x). 
  exists (fun c => if c return Span_sort x ~> shape c then pi1 else pi2).
  done. 
Defined.
Definition Cone_Span (c: Cone): Span a b :=
  span (cone_mor c true) (cone_mor c false).

Lemma _Span_Cone_functor: IsFunctor _ _ Span_Cone.
Proof.
  unshelve eexists.
  - move=>x y h. exists (Spanhom_sort h).
    abstract by case; apply (SpanH h).
  - by move=>x y h h'.
  - by move=>x.
  - by move=>x y z f g.
Defined.
HB.instance Definition _ := _Span_Cone_functor. 

Lemma _Cone_Span_functor: IsFunctor _ _ Cone_Span.
Proof.
  unshelve eexists.
  - move=>x y h. exists (conehom_sort h).
    exact: (conehomP h true, conehomP h false).
  - by move=>x y h h'.
  - by move=>x.
  - by move=>x y z f g.
Defined.
HB.instance Definition _ := _Cone_Span_functor. 

Program Definition Span_Cone_adj: adjunction Span_Cone Cone_Span := Adj.mk _ _ _ _.
Next Obligation.
  unshelve eexists. exact: (fun c => idmap c).
  abstract by (split;split=>x y f; cbn; cat).
Defined.
Next Obligation.
  unshelve eexists. cbn=>c.
  unshelve eexists. cbn. exact: idmap.
  abstract by (case=>/=; rewrite cats).
  abstract by (split; split=>x y f; cbn; rewrite !cats).
Defined.
Next Obligation. cbn=>c. cat. Qed.
Next Obligation. cbn=>c. cat. Qed.
Lemma Span_Cone_refl: Adj.is_reflection Span_Cone_adj.
  unshelve eexists. cbn=>c.
  unshelve eexists. cbn. exact: idmap.
  abstract by (case=>/=; rewrite cats).
  abstract by split; cbn; cat. 
Defined.
Lemma Span_Cone_corefl: Adj.is_coreflection Span_Cone_adj.
  unshelve eexists. exact: (fun c => idmap c).
  abstract by split; cbn; cat. 
Defined.

HB.instance Definition _ := IsPreAdjointF.Build _ _ Span_Cone Cone_Span. 
HB.instance Definition _ := IsLeftAdjoint.Build _ _ Span_Cone Span_Cone_adj. 
HB.instance Definition _ := IsLeftReflection.Build _ _ Span_Cone Span_Cone_refl. 
HB.instance Definition _ := IsLeftCoreflection.Build _ _ Span_Cone Span_Cone_corefl. 
HB.instance Definition _ := IsAdjointEquivalenceL.Build _ _ Span_Cone. 
HB.instance Definition _ := ADJOINTEQUIVALENCE.copy Cone_Span (adj Span_Cone). 

End s.
