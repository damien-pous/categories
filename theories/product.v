(** * products *)

Require Export span.
Require Import arewrite.

Local Open Scope cat_scope.

(** ** products *)

Section s.
Context {𝐂: PreCat} (a b x: ob 𝐂) (p: x ~> a) (q: x ~> b).

Definition product := forall y (p': y ~> a ) (q': y ~> b), unique_sig (spanhom p' q' p q).

Lemma product_terminal: product -> terminal (span_ p q).
Proof. move=>P y. exact: (P y pi1 pi2). Defined.

Lemma terminal_product: terminal (span_ p q) -> product.
Proof. move=>T y p' q'; exact: (T (span_ p' q')). Defined.

End s.
Arguments product {_}.

#[primitive] HB.mixin Record IsProduct (𝐂: PreCat) a b x of SPAN 𝐂 a b x :=
  {#[canonical=no]productP: product a b x pi1 pi2}.
#[short(type=Product)]
HB.structure Definition PRODUCT 𝐂 a b := {x of IsProduct 𝐂 a b x&}. 

Section s.
Context {𝐂: PreCat} (a b: ob 𝐂).

Definition mk_product (x: ob 𝐂) (p: x ~> a) (q: x ~> b) (P: product a b x p q) := span p q.
HB.instance Definition _ x p q H := SPAN.on (@mk_product x p q H). 
HB.instance Definition _ x p q H := IsProduct.Build 𝐂 a b (@mk_product x p q H) H.
Definition mk_product_ x p q H: Product a b := @mk_product x p q H.

Lemma productC x p q: product a b x p q -> product b a x q p.
Proof.
  move=>P y p' q'. move:P=>/(_ y q' p'). apply: unique_sig_impl.
  split; exact: swap_pair.
Defined.

Section s.
Variable (x: Product a b).

(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ :=
  IsTerminal.Build (Span a b) (x: Span _ _) (product_terminal productP).

HB.instance Definition _ :=
  IsProduct.Build 𝐂 b a (spanC x) (productC productP).
Definition ProductC: Product b a := spanC x. 

Section s.
Variables (y: ob 𝐂) (f: y ~> a) (g: y ~> b).
Definition pair: y ~> x := unique_sig_elt (productP y f g). 

Lemma pairE: pair \; pi1 ≡ f ∧ pair \; pi2 ≡ g.
Proof. exact: (unique_sigP (productP y f g)). Qed.

Lemma pair1: pair \; pi1 ≡ f.
Proof. apply pairE. Qed.

Lemma pair2: pair \; pi2 ≡ g.
Proof. apply pairE. Qed.

End s.

Lemma pairU {y} (f: y ~> a) (g: y ~> b) (h: y ~> x):
  h \; pi1 ≡ f -> h \; pi2 ≡ g -> h ≡ pair f g.
Proof.
  move=>F G. symmetry.
  apply: unicity_sig. apply: productP=>//=. exact/pairE.
  by split. 
Qed.

#[export] Instance pair_eqv {y}: Proper (eqv ==> eqv ==> eqv) (@pair y).
Proof.
  move=>f f' ff g g' gg.
  apply: pairU; rewrite -?ff -?gg.
  exact/pair1. exact/pair2.
Qed.

Lemma pair_ext' y (h: y ~> x): h ≡ pair (h \; pi1) (h \; pi2).
Proof. by apply pairU. Qed.

End s.
End s.
Arguments pair {_} [_ _ _ _] _ _.

Section s.
Context {𝐂: Cat}.
Implicit Types a b c d: ob 𝐂.

Section s.
Variables (a b: ob 𝐂) (x: Product a b).
Definition ProductU_Span (y: Product a b): (x: Span a b) ≃ (y: Span a b) :=
  TerminalU _ _.
Definition ProductU (y: Product a b): x ≃ y :=
  Spaniso_sort (ProductU_Span y).
Lemma ProductUH (y: Product a b): @spanhom _ a b x y pi1 pi2 pi1 pi2 (ProductU y)¹.
Proof. exact: SpanH. Qed.

Lemma pair_ext: pair pi1 pi2 ≡ x.
Proof. symmetry. apply: pairU; cat. Qed.

Lemma prod_ext y (f g: y ~> x): f \; pi1 ≡ g \; pi1 -> f \; pi2 ≡ g \; pi2 -> f ≡ g.
Proof. move=>F G. rewrite (pair_ext' g). exact: pairU. Qed.
End s.

Lemma productUr a (u: Terminal 𝐂): product a u a a (term u a).
Proof.
  move=>y p' q'. unshelve apply: mk_unique_sig=>/=. exact: p'.
  split=>/=. cat. exact: termU.
  move=>h [/=<- _]. cat.
Qed.

Lemma productUl a (u: Terminal 𝐂): product u a a (term u a) a.
Proof. apply productC, productUr. Qed.

Lemma productA a b c (ab: Product a b) (bc: Product b c) (x: Product ab c):
  product a bc x (pi1\;pi1) (pair (pi1\;pi2) pi2).
Proof.
(* TODO: finish *)
  move=>y p q. unshelve apply: mk_unique_sig.
  exact: (pair (pair p (q\;pi1)) (q\;pi2)).
  split.
   arewrite pair1; exact: pair1.
   sorry.
  move=>/=h [H1 H2].
  sorry.
Qed.

(* Definition prod_assoc X Y Z: (X×Y)×Z ≃ X×(Y×Z). *)
(* Proof. *)
(*   apply: (mk_iso (pair (fst∘fst) (pair (snd∘fst) snd)) *)
(*             (pair (pair fst (fst∘snd)) (snd∘snd))). *)
(*   - apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) comp1o. *)
(*     by rewrite -compoA !fst_pair. *)
(*     apply prod_ext; rewrite compoA ?(fst_pair,snd_pair)//. *)
(*     by rewrite -compoA fst_pair snd_pair. *)
(*   - apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) comp1o. *)
(*     apply prod_ext; rewrite compoA ?(fst_pair,snd_pair)//. *)
(*     by rewrite -compoA snd_pair fst_pair. *)
(*     by rewrite -compoA !snd_pair. *)
(* Defined. *)


Lemma productA' a b c (ab: Product a b) (bc: Product b c) (x: Product a bc):
  product ab c x (pair pi1 (pi2 \; pi1)) (pi2 \; pi2).
Proof. exact: (productC (@productA c b a (ProductC bc) (ProductC ab) (ProductC x))). Qed.
  
End s.


(** ** categories with terminal objects / binary products / finite products *)
#[primitive] HB.mixin Record Has1 𝐂 of QUIVER 𝐂 := {
    #[canonical=no] one: Terminal 𝐂;
}.
#[short(type="Cat1")]
HB.structure Definition CAT1 := { 𝐂 of CAT 𝐂 & Has1 𝐂}.

#[primitive] HB.mixin Record HasBinaryProducts 𝐂 of PRECAT 𝐂 := {
    #[canonical=no] prod: forall a b: ob 𝐂, Product a b;
  }.

#[short(type="CatBProd")]
HB.structure Definition CATBPROD := { 𝐂 of CAT 𝐂 & HasBinaryProducts 𝐂}.
Infix "×" := prod: cat_scope.

(** also called Cartesian (monoidal) categories *)
#[short(type="CatProd")]
HB.structure Definition CATPROD := { 𝐂 of CAT1 𝐂 & CATBPROD 𝐂}.

Section s.
Context {𝐂: CatBProd}.
Implicit Types a b c d: ob 𝐂.

Definition prodP a b: product a b (a×b) pi1 pi2 := productP. 

Definition pair' a b c d (f: a~>c) (g: b~>d): a×b ~> c×d := pair (pi1\;f) (pi2\;g).

Lemma pair'_id a b: pair' a b ≡ idmap.
Proof. symmetry. apply: pairU; cat. Qed.

Lemma pair'_comp a a' a'' b b' b'' (f: a~>a') (f': a'~>a'') (g: b~>b') (g': b'~>b''):
  pair' (f\;f') (g\;g') ≡ pair' f g \; pair' f' g'.
Proof.
  symmetry; apply: pairU=>/=;
    rewrite !compoA pairE; 
    rewrite -!compoA pairE//.
Qed.

(* Note: could be defined already in PreCatBProd *)
Definition diag a: a ~> a×a := pair a a.

Definition prodC a b: a×b ≃ b×a :=
  ProductU (ProductC _) _.

Definition prodCH a b: spanhom _ _ _ _ (prodC a b)¹ :=
  ProductUH (ProductC _) _.

Definition prodA a b c: (a×b)×c ≃ a×(b×c) :=
  ProductU (mk_product_ (productA _)) _.

Definition prodAH a b c: spanhom _ _ _ _ (prodA a b c)¹ :=
  ProductUH (mk_product_ (productA _)) _.

End s.

Section s.
Context {𝐂: CatProd}.
Implicit Types a b c d: ob 𝐂.

Definition prodUl a: one×a ≃ a :=
  ProductU _ (mk_product_ (@productUl _ _ _)).

Definition prodUlH a: spanhom _ _ _ _ (prodUl a)¹ :=
  ProductUH _ (mk_product_ (@productUl _ _ _)).

Definition prodUr a: a×one ≃ a :=
  ProductU _ (mk_product_ (@productUr _ _ _)).

Definition prodUrH a: spanhom _ _ _ _ (prodUr a)¹ :=
  ProductUH _ (mk_product_ (@productUr _ _ _)).
End s.
