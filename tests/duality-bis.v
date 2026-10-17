(*

duality setup for categories up to span/cospan terminal/initial product/coproduct
not using almost definitional involutivity
nor definitional op equivalence between the categories of spans and cospans

without explicit adjoint equivalences

 *)

Require Import prelim.

Definition ob (C: Type) := C.

#[primitive]
HB.mixin Record IsQuiver C := {
    #[canonical=no] hom: ob C -> ob C -> Type
  }.
#[short(type=Quiver)]
HB.structure Definition QUIVER := {C of IsQuiver C}. 

#[primitive]
HB.mixin Record IsPreCat C of QUIVER C := {
    #[canonical=no] id: forall a: ob C, hom a a;
    #[canonical=no] comp: forall a b c: ob C, hom a b -> hom b c -> hom a c;
  }.
#[short(type=PreCat)]
HB.structure Definition PRECAT := {C of IsPreCat C &}. 
Arguments comp [_ _ _ _]. 

#[primitive]
HB.mixin Record IsCat C of PRECAT C := {
    #[canonical=no] comp1o: forall a b: ob C, forall f: hom a b, comp (id a) f = f;
    #[canonical=no] compo1: forall a b: ob C, forall f: hom b a, comp f (id a) = f;
    #[canonical=no] compoA: forall a b c d: ob C, forall f: hom a b, forall g: hom b c, forall h: hom c d, comp (comp f g) h = comp f (comp g h);
  }.
#[short(type=Cat)]
HB.structure Definition CAT := {C of IsCat C &}. 
Lemma compoA' {C: Cat} (a b c d: ob C) (f: hom b a) (g: hom c b) (h: hom d c): comp h (comp g f) = comp (comp h g) f.
Proof. symmetry. exact/compoA. Qed.

Definition op (C: Type) := C.
Definition obop (C: Quiver) (a: ob C): ob (op C) := a. 
Definition obop' (C: Quiver) (a: ob (op C)): ob C := a. 

HB.instance Definition _ (C: Quiver) := IsQuiver.Build (op C) (fun a b => hom b a).
HB.instance Definition _ (C: PreCat) := IsPreCat.Build (op C) (fun a => id a) (fun a b c f g => comp g f).
HB.instance Definition _ (C: Cat) := IsCat.Build (op C) compo1 comp1o compoA'.

Definition morphop (C: Quiver) (a b: ob C) (f: hom a b): hom (obop b) (obop a) := f. 
Definition morphop' (C: Quiver) (a b: ob (op C)) (f: hom a b): hom (obop' b) (obop' a) := f. 

Fail Check fun C: Quiver => same Quiver C (op (op C)).
Check fun C: PreCat => same Quiver C (op (op C)).
Fail Check fun C: PreCat => same PreCat C (op (op C)).
Check fun C: PreCat => same PreCat (op C) (op (op (op C))).

Check fun C: Cat => same Quiver C (op (op C)).
Check fun C: Cat => same PreCat C (op (op C)).
Fail Check fun C: Cat => same Cat C (op (op C)).
Fail Check fun C: Cat => same Cat (op C) (op (op (op C))). (* needs double compoA *)


#[primitive] HB.mixin Record IsSpan (C: Quiver) (a b: ob C) (x: ob C) := {
    #[canonical=no] pi1: hom x a;
    #[canonical=no] pi2: hom x b;
  }.
#[short(type=Span)]
HB.structure Definition SPAN C a b := {x of IsSpan C a b x}. 
Definition span (C: Quiver) (a b x: ob C) (f: hom x a) (g: hom x b): Span a b :=
  HB.pack x (IsSpan.Build C a b x f g).

#[primitive] HB.mixin Record IsCospan (C: Quiver) (a b: ob C) (x: ob C) := {
    #[canonical=no] in1: hom a x;
    #[canonical=no] in2: hom b x;
  }.
#[short(type=Cospan)]
HB.structure Definition COSPAN C a b := {x of IsCospan C a b x}. 
Definition cospan (C: Quiver) (a b x: ob C) (f: hom a x) (g: hom b x): Cospan a b :=
  HB.pack x (IsCospan.Build C a b x f g).

Fail Check fun (C: Quiver) (a b: ob C) => unify (@Span C a b) (@Cospan (op C) a b).
Fail Check fun (C: Quiver) (a b: ob C) => unify (@Span C a b) (@Cospan (op C) a b).

HB.instance Definition _ C a b (x: @Span C a b) := IsCospan.Build (op C) (obop a) (obop b) (obop x) pi1 pi2. 
HB.instance Definition _ (C: Quiver) (a b: ob C) (x: Span (obop a) (obop b)) := IsCospan.Build C a b (obop' x) (@pi1 _ _ _ x) (@pi2 _ _ _ x).
HB.instance Definition _ C a b (x: @Cospan C a b) := IsSpan.Build (op C) (obop a) (obop b) (obop x) in1 in2.
HB.instance Definition _ (C: Quiver) (a b: ob C) (x: Cospan (obop a) (obop b)) := IsSpan.Build C a b (obop' x) (@in1 _ _ _ x) (@in2 _ _ _ x).
Check fun (C: Quiver) (a b: ob C) (x: Cospan a b) => obop x: Span _ _.   
Check fun (C: Cat) (a b: ob C) (x: Cospan a b) => obop x: Span _ _.   
Check fun (C: Cat) (a b: ob C) (x: Span a b) => obop x: Cospan _ _.   


Section s.
Context {C: PreCat} (a b: ob C).
Definition span_hom (x y: Span a b) := sigT (fun f: hom x y => comp f pi1 = pi1 ∧ comp f pi2 = pi2).
Coercion span_hom_sort x y (f: span_hom x y): hom x y := projT1 f.
Definition span_homP x y (f: span_hom x y): comp f pi1 = pi1 ∧ comp f pi2 = pi2 := projT2 f. 
Definition cospan_hom (x y: Cospan a b) := sigT (fun f: hom x y => comp in1 f = in1 ∧ comp in2 f = in2).
Coercion cospan_hom_sort x y (f: cospan_hom x y): hom x y := projT1 f.
Definition cospan_homP x y (f: cospan_hom x y): comp in1 f = in1 ∧ comp in2 f = in2 := projT2 f. 
HB.instance Definition _ := IsQuiver.Build (Span a b) span_hom. 
HB.instance Definition _ := IsQuiver.Build (Cospan a b) cospan_hom. 
End s.

Definition spanhomop {C: PreCat} (a b: ob C) (x y: Span a b) (f: span_hom x y):
  cospan_hom (obop (y: ob C)) (obop (x: ob C)) := f. 
Definition spanhomop' {C: PreCat} (a b: ob (op C)) (x y: Span a b) (f: span_hom x y):
  cospan_hom (@obop' C y) (@obop' C x) := f. 
Definition cospanhomop {C: PreCat} (a b: ob C) (x y: Cospan a b) (f: cospan_hom x y):
  span_hom (obop (y: ob C)) (obop (x: ob C)) := f. 
Definition cospanhomop' {C: PreCat} (a b: ob (op C)) (x y: Cospan a b) (f: cospan_hom x y):
  span_hom (@obop' C y) (@obop' C x) := f. 

Section s.
Context {C: Cat} (a b: ob C).
Program Definition span_id (x: Span a b): span_hom x x := @existT _ _ (id x) _.
Next Obligation. intro; split; exact: comp1o. Defined.
Program Definition span_comp (x y z: Span a b) (f: span_hom x y) (g: span_hom y z): span_hom x z :=
@existT _ _ (comp f g) _.
Next Obligation. intros; split; by rewrite compoA 2!span_homP. Defined.
HB.instance Definition _ := IsPreCat.Build (Span a b) span_id span_comp. 
HB.instance Definition _ := IsCat.Build (Span a b) sorry sorry sorry. 
End s.

Section s.
Context {C: Cat} (a b: ob C).
Definition cospan_id (x: Cospan a b): cospan_hom x x := span_id (obop (x: ob C)).
Definition cospan_comp (x y z: Cospan a b) (f: cospan_hom x y) (g: cospan_hom y z): cospan_hom x z :=
  span_comp (cospanhomop g) (cospanhomop f). 
HB.instance Definition _ := IsPreCat.Build (Cospan a b) cospan_id cospan_comp. 
HB.instance Definition _ := IsCat.Build (Cospan a b) sorry sorry sorry. 
End s.

(* Check fun (C: Cat) (a b: ob C) => same PreCat (Cospan a b) (op (@Span (op C) a b)). *)
(* Check fun (C: Cat) (a b: ob C) => same PreCat (Span a b) (op (@Cospan (op C) a b)). *)
(* Check fun (C: Cat) (a b: ob C) => same PreCat (op (Cospan a b)) (@Span (op C) a b). *)
(* Check fun (C: Cat) (a b: ob C) => same PreCat (op (Span a b)) (@Cospan (op C) a b). *)

(* Check fun (C: Cat) (a b: ob C) => same Cat (Cospan a b) (op (@Span (op C) a b)). *)
(* Check fun (C: Cat) (a b: ob C) => same Cat (Span a b) (op (@Cospan (op C) a b)). *)
(* Check fun (C: Cat) (a b: ob C) => same Cat (op (Cospan a b)) (@Span (op C) a b). *)
(* Check fun (C: Cat) (a b: ob C) => same Cat (op (Span a b)) (@Cospan (op C) a b). *)


(* we use the dual definitions is_initial/is_terminal instead of relying on IsInitial/IsTerminal
   so that we can get dual definitions is_product/is_coproduct
   and declare the instances product->terminal and coproduct->initial
 *)
Definition is_initial {C: Quiver} (x: ob C) := prod (forall y, hom x y) (forall y (f g: hom x y), f=g).
#[primitive] HB.mixin Record IsInitial (C: Quiver) (x: ob C) :=
  {#[canonical=no]initialP: is_initial x}.
#[short(type=Initial)]
HB.structure Definition INITIAL C := {x of IsInitial C x}. 
Section s.
Context {C: Quiver}.
Definition init (x: Initial C) y: hom x y := fst initialP y. 
Definition initU (x: Initial C) y (f g: hom x y): f = g := snd initialP y f g. 
End s.

Definition is_terminal {C: Quiver} (x: ob C) := prod (forall y, hom y x) (forall y (f g: hom y x), f=g).
#[primitive] HB.mixin Record IsTerminal (C: Quiver) (x: ob C) :=
  {#[canonical=no]terminalP: is_terminal x}.
#[short(type=Terminal)]
HB.structure Definition TERMINAL C := {x of IsTerminal C x}. 
Section s.
Context {C: Quiver}.
Definition term (x: Terminal C) y: hom y x := fst terminalP y. 
Definition termU (x: Terminal C) y (f g: hom y x): f = g := snd terminalP y f g. 
End s.

HB.instance Definition _ C (x: Initial C) := IsTerminal.Build (op C) (obop x) (@initialP _ x).
HB.instance Definition _ C (x: Initial _) := IsTerminal.Build C (obop' x) (@initialP _ x).
HB.instance Definition _ C (x: Terminal C) := IsInitial.Build (op C) (obop x) (@terminalP _ x).
HB.instance Definition _ C (x: Terminal _) := IsInitial.Build C (obop' x) (@terminalP _ x).


Definition is_product {C: PreCat} (a b: ob C) (x: Span a b) := is_terminal x.
#[primitive] HB.mixin Record IsProduct (C: PreCat) a b x of SPAN C a b x :=
  {#[canonical=no]productP: is_product x}.
#[short(type=Product)]
HB.structure Definition PRODUCT C a b := {x of IsProduct C a b x&}. 
Section s.
Context {C: PreCat} (a b: ob C).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Product a b) := IsTerminal.Build (Span a b) (x: Span _ _) productP.
Check fun x: Product a b => x: Span a b.
(* TOTHINK: could work *)
Fail Check fun x: Product a b => x: Terminal (Span a b).
(* TOTHINK: should work *)
Fail Check fun x: Product a b => (x: Span _ _): Terminal (Span a b).
Definition hompair (x: Product a b) y (f: hom y a) (g: hom y b): hom y x :=
  span_hom_sort (term _ (span f g)). 
Lemma hompairE (x: Product a b) y (f: hom y a) (g: hom y b):
  comp (hompair x f g) pi1 = f ∧ comp (hompair x f g) pi2 = g.
Proof. exact/(span_homP (term _ (span f g))). Qed.
End s.

Definition is_coproduct {C: PreCat} (a b: ob C) (x: Cospan a b) := is_initial x.
#[primitive] HB.mixin Record IsCoproduct (C: PreCat) a b x of COSPAN C a b x :=
  {#[canonical=no]coproductP: is_coproduct x}.
#[short(type=Coproduct)]
HB.structure Definition COPRODUCT C a b := {x of IsCoproduct C a b x&}.

(* !! needs explicit op-duality between Span and Cospan *)
Fail HB.instance Definition _ C a b (x: @Product C a b) := IsCoproduct.Build (op C) (obop a) (obop b) (obop x) (@productP _ _ _ x).
Fail HB.instance Definition _ C a b (x: @Coproduct C a b) := IsProduct.Build (op C) (obop a) (obop b) (obop x) (@coproductP _ _ _ x).

(* !! instead we provide explicit conversions *)
Lemma is_coproduct_op C a b x (H: @is_product C a b x): @is_coproduct (op C) (obop a) (obop b) (obop (x: ob C)).
Proof.
  split=>/=y.
  exact: (morphop (fst H (@obop' C y: Span _ _)))=>/=.
  exact: (snd H (@obop' C y: Span _ _))=>/=.
Defined.
Lemma is_product_op C a b x (H: @is_coproduct C a b x): @is_product (op C) (obop a) (obop b)(obop (x: ob C)).
Proof. 
  split=>/=y.
  exact: (morphop (fst H (@obop' C y: Cospan _ _)))=>/=.
  exact: (snd H (@obop' C y: Cospan _ _))=>/=.
Defined.
HB.instance Definition _ C a b (x: @Product C a b) := IsCoproduct.Build (op C) (obop a) (obop b) (obop x) (is_coproduct_op productP).
HB.instance Definition _ C a b (x: @Coproduct C a b) := IsProduct.Build (op C) (obop a) (obop b) (obop x) (is_product_op coproductP).

Fail Check fun (C: Cat) (a b: ob C) (x: Span a b) =>
        unify (@is_product C a b x) (@is_coproduct (op C) a b (obop x)).
Check fun (C: Cat) (a b: ob C) (x: Product a b) => obop x: @Coproduct (op C) a b.

Section s.
Context {C: PreCat} (a b: ob C).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Coproduct a b) := IsInitial.Build (Cospan a b) (x: Cospan _ _) coproductP.
Definition homcopair (x: Coproduct a b) y (f: hom a y) (g: hom b y): hom x y :=
  @hompair (op C) a b (obop x) y f g.
Lemma homcopairE (x: Coproduct a b) y (f: hom a y) (g: hom b y):
  comp in1 (homcopair x f g) = f ∧ comp in2 (homcopair x f g) = g.
Proof. exact/(@hompairE (op C) _ _ (obop x)). Qed.
End s.

Definition spanC (C: Quiver) (a b: ob C) (x: Span a b): ob C := x.
HB.instance Definition _ C a b (x: @Span C a b) := IsSpan.Build C b a (spanC x) pi2 pi1.
Definition span_homC1 (C: PreCat) a b (x: @Span C b a) (y: Span a b) (f: span_hom (spanC x) y): span_hom x (spanC y).
Proof. exists f. apply: swap_pair. exact: (span_homP f). Defined.
Definition span_homC2 (C: PreCat) a b (x: @Span C a b) (y: Span b a) (f: span_hom x (spanC y)): span_hom (spanC x) y.
Proof. exists f. apply: swap_pair. exact: (span_homP f). Defined.

Axiom span_eq: forall C a b x y (f g: @span_hom C a b x y), span_hom_sort f = span_hom_sort g <-> f = g.

Lemma is_productC C a b (x: @Product C a b): is_product (spanC x).
Proof.
  split=>/=y.
  - exact: (span_homC1 (fst (@productP _ _ _ x) (spanC y: Span _ _))).
  - abstract (
      move=>/=f g;
      move:(snd (@productP _ _ _ x) (spanC y: Span _ _) (span_homC2 f) (span_homC2 g))=>/span_eq/=H';
      exact/span_eq/H'). 
Defined.
HB.instance Definition _ C a b (x: Product _ _) := IsProduct.Build C b a (spanC x) (is_productC x).

Definition cospanC (C: Quiver) (a b: ob C) (x: Cospan a b): ob C := x.
HB.instance Definition _ C a b (x: @Cospan C a b) := IsCospan.Build C b a (cospanC x) in2 in1.

Lemma is_coproductC C a b (x: @Coproduct C a b): is_coproduct (cospanC x).
Proof. move: (is_productC (obop x)); exact: is_coproduct_op. Defined.
HB.instance Definition _ C a b (x: Coproduct _ _) := IsCoproduct.Build C b a (cospanC x) (is_coproductC x).

HB.instance Definition _ C (D: Quiver) (f: C -> ob D) :=
  IsQuiver.Build (kernel f) (fun a b => hom (f a) (f b)).
HB.instance Definition _ C (D: PreCat) (f: C -> ob D) :=
  IsPreCat.Build (kernel f) (fun a => id (f a)) (fun a b c => @comp D (f a) (f b) (f c)).
HB.instance Definition _ C (D: Cat) (f: C -> ob D) :=
  IsCat.Build (kernel f)
    (fun a b => @comp1o D (f a) (f b))
    (fun a b => @compo1 D (f a) (f b))
    (fun a b c d => @compoA D (f a) (f b) (f c) (f d)).

Definition fullsub C (P: C -> Prop) := kernel (@sval C P).
HB.instance Definition _ (C: Quiver) (P: C -> Prop) := QUIVER.on (fullsub P). 
HB.instance Definition _ (C: PreCat) (P: C -> Prop) := PRECAT.on (fullsub P). 
HB.instance Definition _ (C: Cat) (P: C -> Prop) := CAT.on (fullsub P).

Definition square (C: PreCat) (a b: ob C) (x: Span a b) (y: Cospan a b) :=
  @comp C x a y pi1 in1 = comp pi2 in2.

#[primitive] HB.mixin Record IsSquareAbove (C: PreCat) (a b y: ob C) (f: hom a y) (g: hom b y) x of SPAN C a b x :=
  {#[canonical=no]squareAbove: square x (cospan f g)}.
#[short(type=SquareAbove)]
HB.structure Definition SQUAREABOVE C a b y f g := {x of IsSquareAbove C a b y f g x&}. 

HB.instance Definition _ (C: PreCat) a b y f g :=
  QUIVER.copy (@SquareAbove C a b y f g) (kernel (@Top_SQUAREABOVE__to__Top_SPAN C a b y f g)). 
HB.instance Definition _ (C: Cat) a b y f g :=
  CAT.copy (@SquareAbove C a b y f g) (kernel (@Top_SQUAREABOVE__to__Top_SPAN C a b y f g)). 

Definition is_pullback (C: PreCat) (a b y: ob C) (f: hom a y) (g: hom b y) (x: SquareAbove f g) := is_terminal x.
#[primitive] HB.mixin Record IsPullback C a b y f g x of @SQUAREABOVE C a b y f g x :=
  {#[canonical=no]pullbackP: is_pullback x}.
#[short(type=Pullback)]
HB.structure Definition PULLBACK C a b y f g := {x of IsPullback C a b y f g x&}. 
Section s.
Context {C: PreCat} (a b y: ob C) (f: hom a y) (g: hom b y).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Pullback f g) := IsTerminal.Build (SquareAbove f g) (x: SquareAbove _ _) pullbackP.
Check fun x: Pullback f g => x: Span a b.
Check fun x: Pullback f g => x: SquareAbove f g.
(* TOTHINK: could work *)
Fail Check fun x: Pullback f g => x: Terminal (SquareAbove f g).
(* TOTHINK: should work *)
Fail Check fun x: Pullback f g => (x: SquareAbove _ _): Terminal (SquareAbove _ _).
End s.

#[primitive] HB.mixin Record IsSquareBelow (C: PreCat) (a b y: ob C) (f: hom y a) (g: hom y b) x of COSPAN C a b x :=
  {#[canonical=no]squareBelow: square (span f g) x}.
#[short(type=SquareBelow)]
HB.structure Definition SQUAREBELOW C a b y f g := {x of IsSquareBelow C a b y f g x&}. 

HB.instance Definition _ (C: PreCat) a b y f g :=
  QUIVER.copy (@SquareBelow C a b y f g) (kernel (@Top_SQUAREBELOW__to__Top_COSPAN C a b y f g)). 
HB.instance Definition _ (C: Cat) a b y f g :=
  CAT.copy (@SquareBelow C a b y f g) (kernel (@Top_SQUAREBELOW__to__Top_COSPAN C a b y f g)). 

Definition is_pushout (C: PreCat) (a b y: ob C) (f: hom y a) (g: hom y b) (x: SquareBelow f g) := is_terminal x.
#[primitive] HB.mixin Record IsPushout C a b y f g x of @SQUAREBELOW C a b y f g x :=
  {#[canonical=no]pushoutP: is_pushout x}.
#[short(type=Pushout)]
HB.structure Definition PUSHOUT C a b y f g := {x of IsPushout C a b y f g x&}. 
Section s.
Context {C: PreCat} (a b y: ob C) (f: hom y a) (g: hom y b).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Pushout f g) := IsTerminal.Build (SquareBelow f g) (x: SquareBelow _ _) pushoutP.
Check fun x: Pushout f g => x: Cospan a b.
Check fun x: Pushout f g => x: SquareBelow f g.
(* TOTHINK: could work *)
Fail Check fun x: Pushout f g => x: Terminal (SquareBelow f g).
(* TOTHINK: should work *)
Fail Check fun x: Pushout f g => (x: SquareBelow _ _): Terminal (SquareBelow _ _).
End s.


Definition is_terminal_op C x (H: @is_terminal C x): @is_initial (op C) (obop x) := H.
Definition is_initial_op C x (H: @is_initial C x): @is_terminal (op C) (obop x) := H.

Definition square_op C a b x y (H: @square C a b x y):
  @square (op C) (obop a) (obop b) (obop (y: ob C)) (obop (x: ob C)) := H.

HB.instance Definition _ C a b y f g (x: @SquareAbove C a b y f g) :=
  IsSquareBelow.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) ((* square_op *) squareAbove).
HB.instance Definition _ C a b y f g (x: @SquareBelow C a b y f g) :=
  IsSquareAbove.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) ((* square_op *) squareBelow).

Lemma is_pullback_op C a b y f g x (H: @is_pullback C a b y f g x):
  @is_pushout (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)).
Admitted.                       (* with explicit op adjunction *)
Lemma is_pushout_op C a b y f g x (H: @is_pushout C a b y f g x):
  @is_pullback (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)).
Admitted.                       (* with explicit op adjunction *)


HB.instance Definition _ C a b y f g (x: @Pullback C a b y f g) :=
  IsPushout.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) (is_pullback_op pullbackP).
HB.instance Definition _ C a b y f g (x: @Pushout C a b y f g) :=
  IsPullback.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) (is_pushout_op pushoutP).


(* HB.instance Definition _ C a b (x: @Coproduct C a b) := IsProduct.Build (op C) (obop a) (obop b) (obop x) (is_product_op coproductP). *)
