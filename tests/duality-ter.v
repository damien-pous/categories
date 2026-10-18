(*

duality setup for categories up to span/cospan terminal/initial product/coproduct pullback/pushout
- with definitional op equivalence for span/cospan terminal/initial product/coproduct pullback/pushout
  (thus without needing explicit adjoint equivalences)
- not requiring definitional involutivity for catop
- nor definitional op equivalence between the categories of spans and cospans

 *)

Require Import prelim.


Axiom sig_eq: forall T (P: T -> Prop) (x y: sig P), sval x = sval y <-> x = y.

Definition unique (T: Type) :=
  prod T (forall x y: T, x=y).

Lemma unique_impl X Y (f: X -> Y) (g: Y -> X) (I: injective g): unique X -> unique Y.
Proof.
  move=>[x U]. split. exact: (f x).
  move=>y y'. exact: I.
Defined.

Lemma unique_impl' X Y (f: X -> Y) (g: Y -> X) (I: cancel g f): unique X -> unique Y.
Proof.
  apply: (unique_impl f). exact: can_inj.
Defined.

Lemma unique_sig_impl T P Q (H: forall x: T, P x <-> Q x): unique (sig P) -> unique (sig Q).
Proof.
  unshelve apply: unique_impl'. 
  1,2: move=>[x H']; exists x; by apply H.
  move=>[??]/=; exact/sig_eq. 
Defined.

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
Definition span (C: Quiver) (a b x: ob C) (f: hom x a) (g: hom x b) := x.
HB.instance Definition _ C a b x f g := IsSpan.Build C a b (@span C a b x f g) f g.
Definition span_ (C: Quiver) (a b x: ob C) (f: hom x a) (g: hom x b): Span a b := span f g.

#[primitive] HB.mixin Record IsCospan (C: Quiver) (a b: ob C) (x: ob C) := {
    #[canonical=no] in1: hom a x;
    #[canonical=no] in2: hom b x;
  }.
#[short(type=Cospan)]
HB.structure Definition COSPAN C a b := {x of IsCospan C a b x}. 
Definition cospan (C: Quiver) (a b x: ob C) (f: hom a x) (g: hom b x) := x.
HB.instance Definition _ C a b x f g := IsCospan.Build C a b (@cospan C a b x f g) f g.
Definition cospan_ (C: Quiver) (a b x: ob C) (f: hom a x) (g: hom b x): Cospan a b := cospan f g.

Fail Check fun (C: Quiver) (a b: ob C) => unify (@Span C a b) (@Cospan (op C) a b).
Fail Check fun (C: Quiver) (a b: ob C) => unify (@Span C a b) (@Cospan (op C) a b).

Section s.
Variables (C: Quiver) (a b: ob C).
HB.instance Definition _ (x: Span a b) := IsCospan.Build (op C) (obop a) (obop b) (obop x) pi1 pi2. 
HB.instance Definition _ (x: Span (obop a) (obop b)) := IsCospan.Build C a b (obop' x) (pi1 (s:=x)) (pi2 (s:=x)).
HB.instance Definition _ (x: @Cospan C a b) := IsSpan.Build (op C) (obop a) (obop b) (obop x) in1 in2.
HB.instance Definition _ (x: Cospan (obop a) (obop b)) := IsSpan.Build C a b (obop' x) (in1 (s:=x)) (in2 (s:=x)).

Definition spanC (x: Span a b): ob C := x.
HB.instance Definition _ x := IsSpan.Build C b a (spanC x) pi2 pi1.
Definition cospanC (x: Cospan a b): ob C := x.
HB.instance Definition _ x := IsCospan.Build C b a (cospanC x) in2 in1.
End s.
Check fun (C: Quiver) (a b: ob C) (x: Cospan a b) => obop x: Span _ _.   
Check fun (C: Cat) (a b: ob C) (x: Cospan a b) => obop x: Span _ _.   
Check fun (C: Cat) (a b: ob C) (x: Span a b) => obop x: Cospan _ _.   




Section s.
Context {C: PreCat} (a b: ob C).
Definition spanhom (x y: ob C) (x1: hom x a) (x2: hom x b) (y1: hom y a) (y2: hom y b) (f: hom x y) :=
  comp f y1 = x1 ∧ comp f y2 = x2.
Definition Spanhom (x y: Span a b) := sig (fun f: hom x y => spanhom pi1 pi2 pi1 pi2 f).
Coercion Spanhom_sort x y (f: Spanhom x y): hom x y := projT1 f.
Definition SpanH x y (f: Spanhom x y): comp f pi1 = pi1 ∧ comp f pi2 = pi2 := projT2 f. 
Definition cospanhom (x y: ob C) (x1: hom a x) (x2: hom b x) (y1: hom a y) (y2: hom b y) (f: hom x y) :=
  comp x1 f = y1 ∧ comp x2 f = y2.
Definition Cospanhom (x y: Cospan a b) := sig (fun f: hom x y => cospanhom in1 in2 in1 in2 f).
Coercion Cospanhom_sort x y (f: Cospanhom x y): hom x y := projT1 f.
Definition CospanH x y (f: Cospanhom x y): comp in1 f = in1 ∧ comp in2 f = in2 := projT2 f. 
HB.instance Definition _ := IsQuiver.Build (Span a b) Spanhom. 
HB.instance Definition _ := IsQuiver.Build (Cospan a b) Cospanhom. 
End s.

Section s.
Context {C: PreCat}.
Definition Spanhomop (a b: ob C) (x y: Span a b) (f: Spanhom x y):
  Cospanhom (obop (y: ob C)) (obop (x: ob C)) := f. 
Definition spanhomop' (a b: ob (op C)) (x y: Span a b) (f: Spanhom x y):
  Cospanhom (@obop' C y) (@obop' C x) := f. 
Definition Cospanhomop (a b: ob C) (x y: Cospan a b) (f: Cospanhom x y):
  Spanhom (obop (y: ob C)) (obop (x: ob C)) := f. 
Definition Cospanhomop' (a b: ob (op C)) (x y: Cospan a b) (f: Cospanhom x y):
  Spanhom (@obop' C y) (@obop' C x) := f. 
End s.

Section s.
Context {C: Cat} (a b: ob C).
Program Definition Span_id (x: Span a b): hom x x := @exist _ _ (id x) _.
Next Obligation. intro; split; exact: comp1o. Qed.
Program Definition Span_comp (x y z: Span a b) (f: hom x y) (g: hom y z): hom x z :=
@exist _ _ (comp f g) _.
Next Obligation. intros; split; by rewrite compoA 2!SpanH. Qed.
HB.instance Definition _ := IsPreCat.Build (Span a b) Span_id Span_comp. 
HB.instance Definition _ := IsCat.Build (Span a b) sorry sorry sorry. 
End s.

Section s.
Context {C: Cat} (a b: ob C).
Definition Cospan_id (x: Cospan a b): hom x x := Span_id (obop (x: ob C)).
Definition Cospan_comp (x y z: Cospan a b) (f: hom x y) (g: hom y z): hom x z :=
  Span_comp (Cospanhomop g) (Cospanhomop f). 
HB.instance Definition _ := IsPreCat.Build (Cospan a b) Cospan_id Cospan_comp. 
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

Section s.
Context {C: PreCat} (a b x: ob C) (p: hom x a) (q: hom x b).
Definition product := forall y (p': hom y a ) (q': hom y b), unique (sig (spanhom p' q' p q)).
Lemma product_terminal: product -> terminal (span_ p q).
Proof. move=>P y. exact: (P y pi1 pi2). Defined.
Lemma terminal_product: terminal (span_ p q) -> product.
Proof. move=>T y q1 q2; exact: (T (span_ q1 q2)). Defined.
End s.

#[primitive] HB.mixin Record IsProduct (C: PreCat) a b x of SPAN C a b x :=
  {#[canonical=no]productP: product (x:=x) pi1 pi2}.
#[short(type=Product)]
HB.structure Definition PRODUCT C a b := {x of IsProduct C a b x&}. 
Section s.
Context {C: PreCat} (a b: ob C).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Product a b) :=
  IsTerminal.Build (Span a b) (x: Span _ _) (product_terminal productP).
Check fun x: Product a b => x: Span a b.
(* TOTHINK: could work *)
Fail Check fun x: Product a b => x: Terminal (Span a b).
(* TOTHINK: should work *)
Fail Check fun x: Product a b => (x: Span _ _): Terminal (Span a b).
Definition hompair (x: Product a b) y (f: hom y a) (g: hom y b): hom y x :=
  Spanhom_sort (term _ (span_ f g)). 
Lemma hompairE (x: Product a b) y (f: hom y a) (g: hom y b):
  comp (hompair x f g) pi1 = f ∧ comp (hompair x f g) pi2 = g.
Proof. exact/(SpanH (term _ (span_ f g))). Qed.
End s.

Section s.
Context {C: PreCat} (a b x: ob C) (i: hom a x) (j: hom b x).
Definition coproduct := forall y (i': hom a y ) (j': hom b y), unique (sig (cospanhom i j i' j')).
Lemma coproduct_initial: coproduct -> initial (cospan_ i j).
Proof. move=>P y; exact: (P y in1 in2). Defined.
Lemma initial_coproduct: initial (cospan_ i j) -> coproduct.
Proof. move=>T y q1 q2; exact: (T (cospan_ q1 q2)). Defined.
End s.

Check fun (C: Cat) (a b: ob C) (x: Span a b) =>
        unify (@product C a b x) (@coproduct (op C) a b (obop x)).

#[primitive] HB.mixin Record IsCoproduct (C: PreCat) a b x of COSPAN C a b x :=
  {#[canonical=no]coproductP: coproduct (x:=x) in1 in2}.
#[short(type=Coproduct)]
HB.structure Definition COPRODUCT C a b := {x of IsCoproduct C a b x&}.

Section s.
Context (C: PreCat) (a b: ob C).
HB.instance Definition _ (x: Product a b) :=
  IsCoproduct.Build (op C) (obop a) (obop b) (obop x) (productP (s:=x)).
HB.instance Definition _ (x: Product (obop a) (obop b)) :=
  IsCoproduct.Build C a b (obop' x) (productP (s:=x)).
HB.instance Definition _ (x: @Coproduct C a b) :=
  IsProduct.Build (op C) (obop a) (obop b) (obop x) (coproductP (s:=x)).
HB.instance Definition _ (x: @Coproduct (op C) (obop a) (obop b)) :=
  IsProduct.Build C a b (obop' x) (coproductP (s:=x)).

Check fun (x: Product a b) => obop x: Coproduct _ _.
Check fun (x: Product a b) => obop x: @Coproduct (op C) a b.

(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Coproduct a b) :=
  IsInitial.Build (Cospan a b) (x: Cospan _ _) (coproduct_initial coproductP).

Definition homcopair (x: Coproduct a b) y (f: hom a y) (g: hom b y): hom x y :=
  @hompair _ _ _ (obop x) y f g.
Lemma homcopairE (x: Coproduct a b) y (f: hom a y) (g: hom b y):
  comp in1 (homcopair x f g) = f ∧ comp in2 (homcopair x f g) = g.
Proof. exact/(hompairE (obop x)). Qed.
End s.

Section s.
Context (C: PreCat) (a b: ob C).

Definition span_homC1 (x: Span b a) (y: Span a b) (f: Spanhom (spanC x) y): Spanhom x (spanC y).
Proof. exists f. apply: swap_pair. exact: (SpanH f). Defined.
Definition span_homC2 (x: Span a b) (y: Span b a) (f: Spanhom x (spanC y)): Spanhom (spanC x) y.
Proof. exists f. apply: swap_pair. exact: (SpanH f). Defined.

Lemma productC x p q: @product C a b x p q -> product q p.
Proof.
  move=>P y p' q'. move:P=>/(_ y q' p'). apply: unique_sig_impl.
  split; exact: swap_pair.
Defined.
HB.instance Definition _ (x: Product _ _) :=
  IsProduct.Build C b a (spanC x) (productC productP).
Definition ProductC (x: @Product C a b): Product b a := spanC x. 

End s.

Section s.
Context (C: PreCat) (a b: ob C).

(* TOTHINK: which option is best? *)
(* first option to dualize ProductC *)
Definition CoproductC (x: Coproduct a b): Coproduct b a :=
  obop' (ProductC (obop x)). 

(* second option to dualize ProductC *)
Lemma coproductC x i j: @coproduct C a b x i j -> coproduct j i.
Proof. exact: (@productC (op C)). Defined.
HB.instance Definition _ (x: Coproduct _ _) :=
  IsCoproduct.Build C b a (cospanC x) (coproductC coproductP).
Definition CoproductC' (x: Coproduct a b): Coproduct b a :=
  cospanC x. 

End s.

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

Definition square (C: PreCat) (a b x y: ob C) (p: hom x a) (q: hom x b) (i: hom a y) (j: hom b y) :=
  comp p i = comp q j.

Lemma squareC C a b x y f g p q: @square C a b x y f g p q -> square g f q p.
Proof. exact: eq_sym. Qed.

#[primitive] HB.mixin Record IsSquareAbove (C: PreCat) (a b y: ob C) (f: hom a y) (g: hom b y) x of SPAN C a b x :=
  {#[canonical=no]squareAbove: @square C a b x y pi1 pi2 f g}.
#[short(type=SquareAbove)]
HB.structure Definition SQUAREABOVE C a b y f g := {x of IsSquareAbove C a b y f g x&}. 
HB.instance Definition _ (C: PreCat) a b y f g :=
  QUIVER.copy (@SquareAbove C a b y f g) (kernel (@Top_SQUAREABOVE__to__Top_SPAN C a b y f g)). 
HB.instance Definition _ (C: Cat) a b y f g :=
  CAT.copy (@SquareAbove C a b y f g) (kernel (@Top_SQUAREABOVE__to__Top_SPAN C a b y f g)). 
Section s.
Context (C: PreCat) (a b x y: ob C)
  (f: hom a y) (g: hom b y) (p: hom x a) (q: hom x b).
Definition square_above (H: square p q f g) := span p q.
HB.instance Definition _ H := SPAN.on (square_above H).
HB.instance Definition _ H := IsSquareAbove.Build C a b y f g (square_above H) H.
Definition square_above_ H: SquareAbove f g := square_above H.
End s.


#[primitive] HB.mixin Record IsSquareBelow (C: PreCat) (a b x: ob C) (f: hom x a) (g: hom x b) y of COSPAN C a b y :=
  {#[canonical=no]squareBelow: @square C a b x y f g in1 in2 }.
#[short(type=SquareBelow)]
HB.structure Definition SQUAREBELOW C a b x f g := {y of IsSquareBelow C a b x f g y&}. 
HB.instance Definition _ (C: PreCat) a b y f g :=
  QUIVER.copy (@SquareBelow C a b y f g) (kernel (@Top_SQUAREBELOW__to__Top_COSPAN C a b y f g)). 
HB.instance Definition _ (C: Cat) a b y f g :=
  CAT.copy (@SquareBelow C a b y f g) (kernel (@Top_SQUAREBELOW__to__Top_COSPAN C a b y f g)). 
Section s.
Context (C: PreCat) (a b x y: ob C)
  (f: hom y a) (g: hom y b) (i: hom a x) (j: hom b x).
Definition square_below (H: square f g i j) := cospan i j.
HB.instance Definition _ H := COSPAN.on (square_below H).
HB.instance Definition _ H := IsSquareBelow.Build C a b y f g (square_below H) H.
Definition square_below_ H: SquareBelow f g := square_below H.
End s.

Section s.
Context (C: PreCat) (a b: ob C).
HB.instance Definition _ y f g (x: @SquareAbove C a b y f g) :=
  IsSquareBelow.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) squareAbove.
HB.instance Definition _ y f g (x: @SquareAbove (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g)) :=
  IsSquareBelow.Build C a b y f g (obop' (x: ob C)) (squareAbove (s:=x)).
HB.instance Definition _ y f g (x: @SquareBelow C a b y f g) :=
  IsSquareAbove.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) squareBelow.
HB.instance Definition _ y f g (x: @SquareBelow (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g)) :=
  IsSquareAbove.Build C a b y f g (obop' (x: ob C)) (squareBelow (s:=x)).
End s.


Section s.
Context (C: PreCat) (a b x y: ob C) (f: hom a y) (g: hom b y) (p: hom x a) (q: hom x b).
Definition is_pullback := 
  square p q f g ∧ 
    forall z (p': hom z a) (q': hom z b), square p' q' f g -> unique (sig (spanhom p' q' p q)).

Lemma pullback_terminal (P: is_pullback): terminal (square_above_ P.1).
Proof. move=>z. exact: (P.2 z pi1 pi2 squareAbove). Defined.
Lemma terminal_pullback H: terminal (@square_above_ C a b x y f g p q H) -> is_pullback.
Proof. move=>T. split=>//z p' q' H'; exact: (T (square_above_ H')). Defined.
End s.

#[primitive] HB.mixin Record IsPullback C a b y f g x of @SQUAREABOVE C a b y f g x :=
  {#[canonical=no]pullbackP: @is_pullback C a b x y f g pi1 pi2}.
#[short(type=Pullback)]
HB.structure Definition PULLBACK C a b y f g := {x of IsPullback C a b y f g x&}. 
Section s.
Context {C: PreCat} (a b y: ob C) (f: hom a y) (g: hom b y).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Pullback f g) := IsTerminal.Build (SquareAbove f g) (x: SquareAbove _ _) (pullback_terminal pullbackP).
Definition pullback x p q (H: is_pullback (x:=x) f g p q) := square_above H.1.
HB.instance Definition _ x p q H := SQUAREABOVE.on (@pullback x p q H). 
HB.instance Definition _ x p q H := IsPullback.Build C a b y f g (@pullback x p q H) H. 
Definition pullback_ x p q H: Pullback f g := @pullback x p q H.
End s.

Section s.
Context (C: PreCat) (a b x y: ob C) (f: hom y a) (g: hom y b) (i: hom a x) (j: hom b x).
Definition is_pushout := 
  square f g i j ∧ 
    forall z (i': hom a z) (j': hom b z), square f g i' j' -> unique (sig (cospanhom i j i' j')).

Lemma pushout_initial (P: is_pushout): initial (square_below_ P.1).
Proof. move=>z. exact: (P.2 z in1 in2 squareBelow). Defined.
Lemma initial_pushout H: initial (@square_below_ C a b x y f g i j H) -> is_pushout.
Proof. move=>T. split=>//z i' j' H'; exact: (T (square_below_ H')). Defined.
End s.

#[primitive] HB.mixin Record IsPushout C a b y f g x of @SQUAREBELOW C a b y f g x :=
  {#[canonical=no]pushoutP: @is_pushout C a b x y f g in1 in2}.
#[short(type=Pushout)]
HB.structure Definition PUSHOUT C a b y f g := {x of IsPushout C a b y f g x&}. 
Section s.
Context {C: PreCat} (a b y: ob C) (f: hom y a) (g: hom y b).
(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ (x: Pushout f g) := IsInitial.Build (SquareBelow f g) (x: SquareBelow _ _) (pushout_initial pushoutP).
Definition pushout x p q (H: is_pushout (x:=x) f g p q) := square_below H.1.
HB.instance Definition _ x p q H := SQUAREBELOW.on (@pushout x p q H). 
HB.instance Definition _ x p q H := IsPushout.Build C a b y f g (@pushout x p q H) H. 
Definition pushout_ x p q H: Pushout f g := @pushout x p q H.
End s.

Section s.
Context (C: PreCat) (a b: ob C).

Lemma is_pullback_op x y f g p q:
  @is_pullback C a b x y f g p q ->
  is_pushout (morphop f) (morphop g) (morphop p) (morphop q).
Proof. exact. Defined.
Lemma is_pushout_op x y f g i j:
  @is_pushout C a b x y f g i j ->
  is_pullback (morphop f) (morphop g) (morphop i) (morphop j).
Proof. exact. Defined.

HB.instance Definition _ y f g (x: @Pullback C a b y f g) :=
  IsPushout.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) ((* is_pullback_op *) pullbackP).
HB.instance Definition _ y f g (x: @Pullback (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g)) :=
  IsPushout.Build C a b y f g (obop' (x: ob C)) (pullbackP (s:=x)).
HB.instance Definition _ y f g (x: @Pushout C a b y f g) :=
  IsPullback.Build (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g) (obop (x: ob C)) ((* is_pushout_op *) pushoutP).
HB.instance Definition _ y f g (x: @Pushout (op C) (obop a) (obop b) (obop y) (morphop f) (morphop g)) :=
  IsPullback.Build C a b y f g (obop' (x: ob C)) (pushoutP (s:=x)).
End s.

Section s.
Context (C: Cat) (a b: ob C).

Lemma is_pullback_id (f: hom a b): is_pullback f (id _) (id _) f.
Proof.
Admitted.

Definition Pullback_id (f: hom a b): Pullback f (id _) :=
  pullback (is_pullback_id f).
End s.                                                

Section s.
Context (C: Cat) (a b: ob C).

Definition Pushout_id (f: hom a b): Pushout f (id _) :=
  obop' (Pullback_id (morphop f)).

Lemma is_pushout_id (f: hom a b): is_pushout f (id _) (id _) f.
Proof. exact: (@is_pullback_id (op C)). Qed.

Definition Pushout_id' (f: hom a b): Pushout f (id _) :=
  pushout (is_pushout_id f).

Fail Check fun f => same (Pushout _ _) (@Pushout_id C a b f) (@Pushout_id' C a b f).
End s.


Lemma is_pullbackC (C: Cat) a b x y f g p q: @is_pullback C a b x y f g p q -> is_pullback g f q p.
Proof.
  move=>P.
  split. apply: squareC. exact: P.1.
  move=>z p' q' H. move: (P.2 z q' p' (squareC H)).
  unshelve apply: unique_impl'.
Admitted.

Definition pullbackC (C: Cat) a b y f g (x: @Pullback C a b y f g): Pullback g f :=
  pullback (is_pullbackC (pullbackP (s:=x))).

Lemma is_pushoutC (C: Cat) a b x y f g p q: @is_pushout C a b x y f g p q -> is_pushout g f q p.
Proof. exact: (@is_pullbackC (op C)). Qed.

Definition pushoutC (C: Cat) a b y f g (x: @Pushout C a b y f g): Pushout g f :=
  obop' (pullbackC (obop x)).
Definition pushoutC' (C: Cat) a b y f g (x: @Pushout C a b y f g): Pushout g f :=
  pushout (is_pushoutC (pushoutP (s:=x))).
