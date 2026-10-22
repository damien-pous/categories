(** * products *)

Require Import cat morphisms span.
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
Arguments product {_} _ _ _ _ _/.

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
  abstract by split; exact: swap_pair.
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

Lemma prod_ext y (f g: y ~> x): f \; pi1 ≡ g \; pi1 ∧ f \; pi2 ≡ g \; pi2 <-> f ≡ g.
Proof.
  split. move=>[F G]. rewrite (pair_ext' g). exact: pairU.
  move=>H. by split; rewrite H.
Qed.
End s.

Program Definition productUr a (u: Terminal 𝐂): product a u a a (term u a) :=
  fun y p' q' => @mk_unique_sig _ _ p' _ _.
Next Obligation. split=>/=. cat. exact: termU. Qed.
Next Obligation. move=>a u y p' q' h [/=<-_]. cat. Qed.

Lemma productUl a (u: Terminal 𝐂): product u a a (term u a) a.
Proof. apply productC, productUr. Defined.

Program Definition productA a b c (ab: Product a b) (bc: Product b c) (x: Product ab c):
  product a bc x (pi1\;pi1) (pair (pi1\;pi2) pi2) :=
  fun y p q => @mk_unique_sig _ _ (pair (pair p (q\;pi1)) (q\;pi2)) _ _.
Next Obligation.
  split.
  - arewrite pair1; exact/pair1.
  - apply/prod_ext; split.
    arewrite pair1; arewrite pair1; exact/pair2.
    arewrite pair2. arewrite pair2. done.
Qed.
Next Obligation.
  move=>/=a b c ab bc x y p q h [<- <-].
  apply/prod_ext; split.
  - arewrite pair1.
     apply/prod_ext; split.
     -- arewrite pair1. cat.
     -- arewrite pair2. arewrite pair1. cat.
  - arewrite pair2. arewrite pair2. done.
Qed.

Lemma productA' a b c (ab: Product a b) (bc: Product b c) (x: Product a bc):
  product ab c x (pair pi1 (pi2 \; pi1)) (pi2 \; pi2).
Proof. exact: (productC (@productA c b a (ProductC bc) (ProductC ab) (ProductC x))). Defined.
  
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

(** [hprod] for "prod" on homsets *)
Definition hprod a b c d (f: a~>c) (g: b~>d): a×b ~> c×d := pair (pi1\;f) (pi2\;g).

#[export] Instance prod_eqv {a b c d}: Proper (eqv ==> eqv ==> eqv) (@hprod a b c d).
Proof. move=>f f' ff g g' gg. apply: pair_eqv; exact/comp_eqv. Qed. 

Lemma prod_id a b: hprod a b ≡ idmap.
Proof. symmetry. apply: pairU; cat. Qed.

Lemma prod_comp a a' a'' b b' b'' (f: a~>a') (f': a'~>a'') (g: b~>b') (g': b'~>b''):
  hprod (f\;f') (g\;g') ≡ hprod f g \; hprod f' g'.
Proof.
  symmetry; apply: pairU=>/=;
    rewrite !compoA pairE; 
    rewrite -!compoA pairE//.
Qed.

Lemma prod1 a b c d (f: a~>c) (g: b~>d): hprod f g \; pi1 ≡ pi1 \; f.
Proof. by rewrite /hprod pair1. Qed.

Lemma prod2 a b c d (f: a~>c) (g: b~>d): hprod f g \; pi2 ≡ pi2 \; g.
Proof. by rewrite /hprod pair2. Qed.

Lemma prodE a b c d (f: a~>c) (g: b~>d): hprod f g \; pi1 ≡ pi1 \; f ∧ hprod f g \; pi2 ≡ pi2 \; g.
Proof. split. exact/prod1. exact/prod2. Qed.


(** [hprod] preserves monos (but not epis)
    as a functor, it also preserves split epis, split monos, and isomorphisms *)

Lemma prod_mono a a' b b' (f: Mono a a') (g: Mono b b'): is_mono (hprod f g).
Proof.
  move=>/=c i j /prod_ext[++].
  rewrite !compoA /hprod !pairE -!compoA.
  move=>/monoP?/monoP?. exact/prod_ext.
Qed.
HB.instance Definition _ a a' b b' (f: Mono a a') (g: Mono b b') :=
  IsMono.Build _ _ _ (hprod f g) (@prod_mono _ _ _ _ f g).

HB.instance Definition _ a a' b b' (f: Invertible a a') (g: Invertible b b') :=
  HasInverseOp.Build _ _ _ (hprod f g) (hprod f⁻¹ g⁻¹). 

Lemma prod_splitmono a a' b b' (f: SplitMono a a') (g: SplitMono b b'): has_right_inverse (hprod f g).
Proof. by rewrite/=-prod_comp 2!invKr prod_id. Qed.

HB.instance Definition _ a a' b b' (f: SplitMono a a') (g: SplitMono b b') :=
  HasRightInverse.Build _ _ _ (hprod f g) (@prod_splitmono _ _ _ _ f g).

Lemma prod_splitepi a a' b b' (f: SplitEpi a a') (g: SplitEpi b b'): has_left_inverse (hprod f g).
Proof. by rewrite/=-prod_comp 2!invKl prod_id. Qed.

HB.instance Definition _ a a' b b' (f: SplitEpi a a') (g: SplitEpi b b') :=
  HasLeftInverse.Build _ _ _ (hprod f g) (@prod_splitepi _ _ _ _ f g).

HB.saturate hprod.
Definition prod_iso a a' b b' (f: a ≃ a') (g: b ≃ b'): a×b ≃ a'×b' := hprod f g.

(* local notation, consistent with the subsequent notation in (cartesian) monoidal categories *)
Infix "·" := hprod: cat_scope.

(* Note: could be defined already in PreCatBProd *)
Definition diag a: a ~> a×a := pair a a.

Definition prodC a b: a×b ≃ b×a :=
  ProductU (ProductC _) _.

Definition prodCH a b: spanhom _ _ _ _ (prodC a b)¹ :=
  ProductUH (ProductC _) _.

Lemma prodC1 a b: prodC a b \; pi1 ≡ pi2.
Proof. apply prodCH. Qed.

Lemma prodC2 a b: prodC a b \; pi2 ≡ pi1.
Proof. apply prodCH. Qed.

Lemma prodC_nat a b a' b' f g: g · f \; prodC b' a' ≡ prodC a b \; f · g.
Proof.
  apply/prod_ext. split.
  by rewrite compoA prodC1 prod2 compoA prod1 -compoA prodC1.
  by rewrite compoA prodC2 prod1 compoA prod2 -compoA prodC2.
Qed.

Definition prodA a b c: (a×b)×c ≃ a×(b×c) :=
  ProductU (mk_product_ (productA _)) _.

Definition prodAH a b c: spanhom _ _ _ _ (prodA a b c)¹ :=
  ProductUH (mk_product_ (productA _)) _.

Lemma prodA1 a b c: prodA a b c \; pi1 ≡ pi1 \; pi1.
Proof. apply prodAH. Qed.

Lemma prodA2 a b c: prodA a b c \; pi2 \; pi1 ≡ pi1 \; pi2.
Proof. by rewrite -compoA (prodAH a b c).2 pair1. Qed.

Lemma prodA3 a b c: prodA a b c \; pi2 \; pi2 ≡ pi2.
Proof. by rewrite -compoA (prodAH a b c).2 pair2. Qed.

Lemma prodA_nat a b c a' b' c' f g h:
  (f · g) · h \; prodA a' b' c' ≡ prodA a b c \; f · (g · h).
Proof.
  apply/prod_ext; split. 2: apply/prod_ext; split.
  - arewrite prodA1. arewrite prod1. arewrite prod1. symmetry.
    arewrite prod1. arewrite prodA1. cat.
  - arewrite prodA2. arewrite prod1. arewrite prod2. symmetry.
    arewrite prod2. arewrite prod1. arewrite prodA2. cat.
  - arewrite prodA3. arewrite prod2. symmetry.
    arewrite prod2. arewrite prod2. arewrite prodA3. cat.
Qed.

Lemma prodA_pentagon a b c d:
  prodA a b c · d \; prodA a (b × c) d \; a · prodA b c d ≡ prodA (a × b) c d \; prodA a b (c × d).
Proof.
  apply/prod_ext; split. 2: apply/prod_ext; split. 3: apply/prod_ext; split.
  - arewrite prod1. arewrite prodA1. arewrite prod1. arewrite prodA1. symmetry.
    arewrite prodA1. arewrite prodA1. cat.
  - arewrite prod2. arewrite prodA1. arewrite prodA2. arewrite prod1. arewrite prodA2. symmetry.
    arewrite prodA2. arewrite prodA1. cat.
  - arewrite prod2. arewrite prodA2. arewrite prodA2. arewrite prod1. arewrite prodA3. symmetry.
    arewrite prodA3. arewrite prodA2. done. 
  - arewrite prod2. arewrite prodA3. arewrite prodA3. arewrite prod2. symmetry.
    arewrite prodA3. arewrite prodA3. cat. 
Qed.

End s.

Section s.
Context {𝐂: CatProd}.
Implicit Types a b c d: ob 𝐂.
Infix "·" := hprod: cat_scope.

Definition prodUl a: one×a ≃ a :=
  ProductU _ (mk_product_ (@productUl _ _ _)).

Definition prodUlH a: spanhom _ _ _ _ (prodUl a)¹ :=
  ProductUH _ (mk_product_ (@productUl _ _ _)).

Lemma prodUl'2 a: inv (prodUl a) \; pi2 ≡ idmap.
Proof. rewrite -iso_src. symmetry. apply prodUlH. Qed.

Lemma prodUl_pi2 a: (prodUl a)¹ ≡ pi2.
Proof. move: (prodUl'2 a). rewrite iso_src. move=>->. cat. Qed.

Lemma prodUl_nat a a' f: idmap · f \; prodUl a' ≡ prodUl a \; f.
Proof.
  rewrite iso_tgt compoA iso_src. 
  apply/prod_ext; split. exact/termU.
  arewrite prod2. arewrite prodUl'2. symmetry.
  arewrite prodUl'2. cat.
Qed.

Definition prodUr a: a×one ≃ a :=
  ProductU _ (mk_product_ (@productUr _ _ _)).

Definition prodUrH a: spanhom _ _ _ _ (prodUr a)¹ :=
  ProductUH _ (mk_product_ (@productUr _ _ _)).

(* to be deduced from monoidal symmetry? *)
Lemma prodUr'1 a: inv (prodUr a) \; pi1 ≡ idmap.
Proof. rewrite -iso_src. symmetry. apply prodUrH. Qed.

Lemma prodUr_pi1 a: (prodUr a)¹ ≡ pi1.
Proof. move: (prodUr'1 a). rewrite iso_src. move=>->. cat. Qed.

Lemma prodUr_nat a a' f: f · idmap \; prodUr a' ≡ prodUr a \; f.
Proof.
  rewrite iso_tgt compoA iso_src. 
  apply/prod_ext; split. 2: exact/termU. 
  arewrite prod1. arewrite prodUr'1. symmetry. 
  arewrite prodUr'1. cat. 
Qed.

Lemma prodA_triangle a b: prodA a one b \; a · prodUl b ≡ prodUr a · b.
Proof.
  apply/prod_ext; split. 
  - arewrite prod1. arewrite prodA1. symmetry.
    arewrite prod1. arewrite prodUr_pi1. done. 
  - arewrite prod2. arewrite prodUl_pi2. arewrite prodA3. symmetry.
    arewrite prod2. cat.
Qed.

End s.
