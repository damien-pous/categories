(*

duality setup for categories up to span/cospan terminal/initial product/coproduct
here getting almost definitional involutivity
and definitional op equivalence between the categories of spans and cospans

systematically using:
plain defs (is_quiver,is_precat,is_cat,is_span...) using primitive sigma types and products
+ HB packages for inferrence

nice but rather fragile:
- requires trick for associativity
- needs two names for span/cospan (plain defs) and Span/Cospan (HB records)
- slow comparisons for some dualities (deep records + proof comparisons)

 *)

Require Import prelim.

Fail Check fun A P (V: @sigT A P) => unify V (existT _ _ (projT2 V)).
Fail Check fun A B (p: A /\ B) => unify p (conj p.1 p.2).
Fail Check fun A B (p: prod A B) => unify p (p.1,p.2).
Set Primitive Projections.
Record sigT A (P: A -> Type) := existT {projT1: A; projT2: P projT1}. 
Record prod A B := pair {fst: A; snd: B}. 
Unset Primitive Projections.
Check fun A P (V: @sigT A P) => unify V (existT (projT2 V)).
Check fun A B (p: prod A B) => unify p (pair (fst p) (snd p)).
Coercion conjprod {A B} (p: A /\ B) := (proj1 p, proj2 p).

Definition ob (C: Type) := C.

Definition quiver_on C := ob C -> ob C -> Type.
#[primitive]
HB.mixin Record IsQuiver C := {#[canonical=no]quiverP: quiver_on C}.
#[short(type=Quiver)]
HB.structure Definition QUIVER := {C of IsQuiver C}. 
Definition hom {C: Quiver}: ob C -> ob C -> Type := @quiverP C. 

Definition precat_on (C: Quiver) :=
  prod (forall a: ob C, hom a a) (forall a b c: ob C, hom a b -> hom b c -> hom a c).
#[primitive]
HB.mixin Record IsPreCat C of QUIVER C := {#[canonical=no]precatP: precat_on C}.
#[short(type=PreCat)]
HB.structure Definition PRECAT := {C of IsPreCat C &}. 
Definition id {C: PreCat}: forall a: ob C, hom a a := fst precatP. 
Definition comp {C: PreCat}: forall a b c: ob C, hom a b -> hom b c -> hom a c := snd precatP. 

Definition cat_on (C: PreCat) :=
  prod
  (prod
    (forall a b: ob C, forall f: hom a b, comp (id a) f = f)
    (forall a b: ob C, forall f: hom b a, comp f (id a) = f))
  (prod
    (forall a b c d: ob C, forall f: hom a b, forall g: hom b c, forall h: hom c d, comp (comp f g) h = comp f (comp g h))
    (forall a b c d: ob C, forall f: hom b a, forall g: hom c b, forall h: hom d c, comp h (comp g f) = comp (comp h g) f)).
#[primitive]
HB.mixin Record IsCat C of PRECAT C := {#[canonical=no]catP: cat_on C}.
#[short(type=Cat)]
HB.structure Definition CAT := {C of IsCat C &}. 
Definition comp1o {C: Cat}: forall a b: ob C, forall f: hom a b, comp (id a) f = f := fst (fst catP).
Definition compo1 {C: Cat}: forall a b: ob C, forall f: hom b a, comp f (id a) = f := snd (fst catP).
Definition compoA {C: Cat}: forall a b c d: ob C, forall f: hom a b, forall g: hom b c, forall h: hom c d, comp (comp f g) h = comp f (comp g h) := fst (snd catP).
Definition compoA'{C: Cat}: forall a b c d: ob C, forall f: hom b a, forall g: hom c b, forall h: hom d c, comp h (comp g f) = comp (comp h g) f := snd (snd catP).

Definition op (C: Type) := C.

Definition quiver_op {C: Quiver}: quiver_on (op C) := fun a b => hom b a.
HB.instance Definition _ (C: Quiver) := IsQuiver.Build (op C) quiver_op.

Fail Check fun C: Quiver => same Quiver C (op (op C)).

Definition precat_op {C: PreCat}: precat_on (op C) := pair (fun a => id a) (fun a b c f g => comp g f).
HB.instance Definition _ (C: PreCat) := IsPreCat.Build (op C) precat_op.

Check fun C: PreCat => same Quiver C (op (op C)).
Fail Check fun C: PreCat => same PreCat C (op (op C)).
Check fun C: PreCat => same PreCat (op C) (op (op (op C))).

Definition cat_op {C: Cat}: cat_on (op C) :=
  pair
    (pair (@compo1 C) (@comp1o C))
    (pair (@compoA' C) (@compoA C)).
HB.instance Definition _ (C: Cat) := IsCat.Build (op C) cat_op.

Check fun C: Cat => same Quiver C (op (op C)).
Check fun C: Cat => same PreCat C (op (op C)).
Fail Check fun C: Cat => same Cat C (op (op C)).
Check fun C: Cat => same Cat (op C) (op (op (op C))).



Definition span_on (C: Quiver) (a b: ob C) (x: ob C) := prod (hom x a) (hom x b).
Definition span (C: Quiver) (a b: ob C) := sigT (span_on a b).
Definition mk_span(C: Quiver) (a b x: ob C) (f: hom x a) (g: hom x b): span a b := existT (pair f g).
Coercion span_sort (C: Quiver) (a b: ob C) (x: span a b): ob C := projT1 x.
#[primitive] HB.mixin Record IsSpan (C: Quiver) (a b: ob C) (x: ob C) :=
  {#[canonical=no]spanP: span_on a b x}.
#[short(type=Span)]
HB.structure Definition SPAN C a b := {x of IsSpan C a b x}. 
Section s.
Context {C: Quiver} {a b: ob C}.
HB.instance Definition _ (x: span a b) := IsSpan.Build C a b x (projT2 x).
Definition span_pack (x: Span a b): span a b := existT (@spanP _ _ _ x). 
Definition pi1 {x: Span a b}: hom x a := fst spanP. 
Definition pi2 {x: Span a b}: hom x b := snd spanP.
End s.

Definition cospan_on (C: Quiver) (a b: ob C) (x: ob C) := prod (hom a x) (hom b x).
Definition cospan (C: Quiver) (a b: ob C) := sigT (cospan_on a b).
Definition mk_cospan(C: Quiver) (a b x: ob C) (f: hom a x) (g: hom b x): cospan a b := existT (pair f g).
Coercion cospan_sort (C: Quiver) (a b: ob C) (x: cospan a b): ob C := projT1 x.
#[primitive] HB.mixin Record IsCospan (C: Quiver) (a b: ob C) (x: ob C) :=
  {#[canonical=no]cospanP: cospan_on a b x}.
#[short(type=Cospan)]
HB.structure Definition COSPAN C a b := {x of IsCospan C a b x}. 
Section s.
Context {C: Quiver} {a b: ob C}.
HB.instance Definition _ (x: cospan a b) := IsCospan.Build C a b x (projT2 x).
Definition cospan_pack (x: Cospan a b): cospan a b := existT (@cospanP _ _ _ x). 
Definition in1 {x: Cospan a b}: hom a x := fst cospanP. 
Definition in2 {x: Cospan a b}: hom b x := snd cospanP. 
End s.

Check fun (C: Quiver) (a b: ob C) => unify (@span C a b) (@cospan (op C) a b).
Fail Check fun (C: Quiver) (a b: ob C) => unify (@Span C a b) (@Cospan (op C) a b).

Section s.
Context {C: PreCat} {a b: ob C}.
Definition span_hom (x y: span a b) := sigT (fun f: hom x y => comp f pi1 = pi1 /\ comp f pi2 = pi2).
Coercion span_hom_sort x y (f: span_hom x y): hom x y := projT1 f.
Definition span_homP x y (f: span_hom x y): comp f pi1 = pi1 ∧ comp f pi2 = pi2 := projT2 f. 
Definition cospan_hom (x y: cospan a b) := sigT (fun f: hom x y => comp in1 f = in1 /\ comp in2 f = in2).
Coercion cospan_hom_sort x y (f: cospan_hom x y): hom x y := projT1 f.
Definition cospan_homP x y (f: cospan_hom x y): comp in1 f = in1 ∧ comp in2 f = in2 := projT2 f. 
HB.instance Definition _ := IsQuiver.Build (span a b) span_hom. 
HB.instance Definition _ := IsQuiver.Build (cospan a b) cospan_hom. 
End s.

Section s.
Context {C: Cat} {a b: ob C}.
Program Definition span_id (x: span a b): span_hom x x := @existT _ _ (id x) _.
Next Obligation. intro; split; exact: comp1o. Defined.
Program Definition span_comp (x y z: span a b) (f: span_hom x y) (g: span_hom y z): span_hom x z :=
@existT _ _ (comp f g) _.
Next Obligation. intros; split; by rewrite compoA 2!span_homP. Defined.
Definition span_precat: precat_on (span a b) := pair span_id span_comp.
HB.instance Definition _ := IsPreCat.Build (span a b) span_precat. 
Lemma span_cat: cat_on (span a b).
Proof.
  split; split; cbn.
  - sorry.
  - sorry.
  - sorry.
  - sorry.
Defined. 
HB.instance Definition _ := IsCat.Build (span a b) span_cat. 
End s.

Section s.
Context {C: Cat} {a b: ob C}.
Definition cospan_id (x: cospan a b): cospan_hom x x := @span_id (op C) a b x.
Definition cospan_comp (x y z: cospan a b) (f: cospan_hom x y) (g: cospan_hom y z): cospan_hom x z :=
  @span_comp (op C) a b z y x g f. 
Definition cospan_precat: precat_on (cospan a b) := @precat_op (@span (op C) a b).
HB.instance Definition _ := IsPreCat.Build (cospan a b) cospan_precat. 
Definition cospan_cat: cat_on (cospan a b) := @cat_op (@span (op C) a b).
HB.instance Definition _ := IsCat.Build (cospan a b) cospan_cat. 
End s.

Check fun (C: Cat) (a b: ob C) => same PreCat (cospan a b) (op (@span (op C) a b)).
Check fun (C: Cat) (a b: ob C) => same PreCat (span a b) (op (@cospan (op C) a b)).
Check fun (C: Cat) (a b: ob C) => same PreCat (op (cospan a b)) (@span (op C) a b).
Check fun (C: Cat) (a b: ob C) => same PreCat (op (span a b)) (@cospan (op C) a b).

Check fun (C: Cat) (a b: ob C) => same Cat (cospan a b) (op (@span (op C) a b)).
Check fun (C: Cat) (a b: ob C) => same Cat (span a b) (op (@cospan (op C) a b)).
Check fun (C: Cat) (a b: ob C) => same Cat (op (cospan a b)) (@span (op C) a b).
Check fun (C: Cat) (a b: ob C) => same Cat (op (span a b)) (@cospan (op C) a b).

Definition obop (C: Quiver) (a: ob C): ob (op C) := a. 
HB.instance Definition _ C a b (x: @Span C a b) := IsCospan.Build (op C) a b (obop x) (@spanP _ _ _ x).
HB.instance Definition _ C a b (x: @Cospan C a b) := IsSpan.Build (op C) a b (obop x) (@cospanP _ _ _ x).


Definition is_initial {C: Quiver} (x: ob C) := prod (forall y, hom x y) (forall y (f g: hom x y), f=g).
#[primitive] HB.mixin Record IsInitial (C: Quiver) (x: ob C) :=
  {#[canonical=no]initialP: is_initial x}.
#[short(type=Initial)]
HB.structure Definition INITIAL C := {x of IsInitial C x}. 
Section s.
Context {C: Quiver}.
Definition init {x: Initial C} y: hom x y := fst initialP y. 
Definition initU {x: Initial C} y (f g: hom x y): f = g := snd initialP y f g. 
End s.

Definition is_terminal {C: Quiver} (x: ob C) := prod (forall y, hom y x) (forall y (f g: hom y x), f=g).
#[primitive] HB.mixin Record IsTerminal (C: Quiver) (x: ob C) :=
  {#[canonical=no]terminalP: is_terminal x}.
#[short(type=Terminal)]
HB.structure Definition TERMINAL C := {x of IsTerminal C x}. 
Section s.
Context {C: Quiver}.
Definition term {x: Terminal C} y: hom y x := fst terminalP y. 
Definition termU {x: Terminal C} y (f g: hom y x): f = g := snd terminalP y f g. 
End s.

HB.instance Definition _ C (x: Initial C) := IsTerminal.Build (op C) (obop x) (@initialP _ x).
HB.instance Definition _ C (x: Terminal C) := IsInitial.Build (op C) (obop x) (@terminalP _ x).


Definition is_product {C: Cat} (a b: ob C) (x: Span a b) := is_terminal (span_pack x).
#[primitive] HB.mixin Record IsProduct (C: Cat) (a b: ob C) x of SPAN C a b x :=
  {#[canonical=no]productP: is_product x}.
#[short(type=Product)]
HB.structure Definition PRODUCT C a b := {x of IsProduct C a b x&}. 
Section s.
Context {C: Cat} (a b: ob C).
HB.instance Definition _ (x: Product a b) := IsTerminal.Build (span a b) (span_pack x) productP.
Check fun x: Product a b => x: Span a b.
Fail Check fun x: Product a b => x: Terminal (span a b).
(* TOTHINK: should work *)
Fail Check fun x: Product a b => span_pack x: Terminal (span a b).
(* TOTHINK: could work *)
Fail Definition hompair (x: Product a b) y (f: hom y a) (g: hom y b): hom y x :=
  span_hom_sort (term (mk_span f g)). 
(* TOTHINK: should work *)
Fail Definition hompair (x: Product a b) y (f: hom y a) (g: hom y b): hom y x :=
  span_hom_sort (@term _ (span_pack x) (mk_span f g)).
(* FRAGILE *)
Definition hompair (x: Product a b) y (f: hom y a) (g: hom y b): hom y x :=
  span_hom_sort (@term _ (Top_span_pack__canonical__Top_TERMINAL x) (mk_span f g)). 
Lemma hompairE (x: Product a b) y (f: hom y a) (g: hom y b):
  comp (hompair x f g) pi1 = f ∧ comp (hompair x f g) pi2 = g.
Proof.
  exact/(span_homP (@term _ (Top_span_pack__canonical__Top_TERMINAL x) (mk_span f g))).
Qed.
  
End s.

Definition is_coproduct {C: Cat} (a b: ob C) (x: Cospan a b) := is_initial (cospan_pack x).
#[primitive] HB.mixin Record IsCoproduct (C: Cat) (a b: ob C) x of COSPAN C a b x :=
  {#[canonical=no]coproductP: is_coproduct x}.
#[short(type=Coproduct)]
HB.structure Definition COPRODUCT C a b := {x of IsCoproduct C a b x&}.

HB.instance Definition _ C a b (x: @Product C a b) := IsCoproduct.Build (op C) a b (obop x) (@productP _ _ _ x).
HB.instance Definition _ C a b (x: @Coproduct C a b) := IsProduct.Build (op C) a b (obop x) (@coproductP _ _ _ x).

Check fun (C: Cat) (a b: ob C) (x: Span a b) =>
        unify (@is_product C a b x) (@is_coproduct (op C) a b (obop x)).
Check fun (C: Cat) (a b: ob C) (x: Product a b) => obop x: @Coproduct (op C) a b.

Section s.
Context {C: Cat} (a b: ob C).
HB.instance Definition _ (x: Coproduct a b) := IsInitial.Build (cospan a b) (cospan_pack x) coproductP.
Definition homcopair (x: Coproduct a b) y (f: hom a y) (g: hom b y): hom x y :=
  @hompair (op C) a b (obop x) y f g.
Lemma homcopairE (x: Coproduct a b) y (f: hom a y) (g: hom b y):
  comp in1 (homcopair x f g) = f ∧ comp in2 (homcopair x f g) = g.
Proof. exact/(@hompairE (op C) _ _ (obop x)). Qed.
End s.

