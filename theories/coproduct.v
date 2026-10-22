(** * coproducts *)

Require Import cat morphisms span cospan product.

Local Open Scope cat_scope.

(** ** products *)

Section s.
Context {𝐂: PreCat} (a b x: ob 𝐂) (i: a ~> x) (j: b ~> x).

Definition coproduct := forall y (i': a ~> y ) (j': b ~> y), unique_sig (cospanhom i j i' j').

Lemma coproduct_initial: coproduct -> initial (cospan_ i j).
Proof. move=>P y. exact: (P y in1 in2). Defined.

Lemma initial_coproduct: initial (cospan_ i j) -> coproduct.
Proof. move=>T y i' j'; exact: (T (cospan_ i' j')). Defined.

End s.
Arguments coproduct {_} _ _ _ _ _/.

#[primitive] HB.mixin Record IsCoproduct (𝐂: PreCat) a b x of COSPAN 𝐂 a b x :=
  {#[canonical=no]coproductP: coproduct a b x in1 in2}.
#[short(type=Coproduct)]
HB.structure Definition COPRODUCT 𝐂 a b := {x of IsCoproduct 𝐂 a b x&}. 

Section s.
Context (𝐂: PreCat) (a b: ob 𝐂).

Definition mk_coproduct (x: ob 𝐂) (i: a ~> x) (j: b ~> x) (P: coproduct a b x i j) := cospan i j.
HB.instance Definition _ x i j H := COSPAN.on (@mk_coproduct x i j H). 
HB.instance Definition _ x i j H := IsCoproduct.Build 𝐂 a b (@mk_coproduct x i j H) H.
Definition mk_coproduct_ x i j H: Coproduct a b := @mk_coproduct x i j H.

Lemma product_op x f g: @product _ _ _ _ (morphop f) (morphop g) -> @coproduct 𝐂 a b x f g.
Proof. exact. Defined.
Lemma coproduct_op x f g: @coproduct _ _ _ _ (morphop f) (morphop g) -> @product 𝐂 a b x f g.
Proof. exact. Defined.

HB.instance Definition _ (x: Product a b) :=
  IsCoproduct.Build 𝐂^op (obop a) (obop b) (obop x) (productP (s:=x)).
HB.instance Definition _ (x: Product (obop a) (obop b)) :=
  IsCoproduct.Build 𝐂 a b (obop' x) (productP (s:=x)).
HB.instance Definition _ (x: Coproduct a b) :=
  IsProduct.Build 𝐂^op (obop a) (obop b) (obop x) (coproductP (s:=x)).
HB.instance Definition _ (x: Coproduct (obop a) (obop b)) :=
  IsProduct.Build 𝐂 a b (obop' x) (coproductP (s:=x)).

Lemma coproductC x i j: coproduct a b x i j -> coproduct b a x j i.
Proof. exact: (@productC 𝐂^op). Defined.

Section s.
Context (x: Coproduct a b).

(* TOTHINK: fragile instance declaration, almost non-forgetful *)
HB.instance Definition _ :=
  IsInitial.Build (Cospan a b) (x: Cospan _ _) (coproduct_initial coproductP).

HB.instance Definition _ :=
  IsCoproduct.Build 𝐂 b a (cospanC x) (coproductC coproductP).
Definition CoproductC: Coproduct b a := cospanC x. 

Section s.
Variables (y: ob 𝐂) (f: a ~> y) (g: b ~> y).
Definition copair: x ~> y := @pair _ _ _ (obop x) y f g.

Lemma copairE: in1 \; copair ≡ f ∧ in2 \; copair ≡ g.
Proof. exact/(pairE (obop x)). Qed.

Lemma copair1: in1 \; copair ≡ f.
Proof. apply copairE. Qed.

Lemma copair2: in2 \; copair ≡ g.
Proof. apply copairE. Qed.

End s.

Lemma copairU {y} (f: a ~> y) (g: b ~> y) (h: x ~> y):
  in1 \; h ≡ f -> in2 \; h ≡ g -> h ≡ copair f g.
Proof. exact: (pairU (x:=obop x)). Qed.

#[export] Instance copair_eqv {y}: Proper (eqv ==> eqv ==> eqv) (@copair y).
Proof. exact: (@pair_eqv 𝐂^op). Qed.

Lemma copair_ext' y (h: x ~> y): h ≡ copair (in1 \; h) (in2 \; h).
Proof. by apply copairU. Qed.

End s.
End s.
Arguments copair {_} [_ _ _ _] _ _.

Section s.
Context {𝐂: Cat}.
Implicit Types a b c d: ob 𝐂.

Section s.
Variables (a b: ob 𝐂) (x: Coproduct a b).
Definition CoproductU_Cospan (y: Coproduct a b): (x: Cospan a b) ≃ (y: Cospan a b) :=
  InitialU _ _.
Definition CoproductU (y: Coproduct a b): x ≃ y :=
  Cospaniso_sort (CoproductU_Cospan y).
Lemma CoproductUH (y: Coproduct a b): @cospanhom _ a b x y in1 in2 in1 in2 (CoproductU y)¹.
Proof. exact: CospanH. Qed.

Lemma copair_ext: copair in1 in2 ≡ x.
Proof. exact: (pair_ext (obop x)). Qed.

Lemma coprod_ext y (f g: x ~> y): in1 \; f ≡ in1 \; g ∧ in2 \; f ≡ in2 \; g <-> f ≡ g.
Proof. exact: (prod_ext (x:=obop x)). Qed.
End s.

Lemma coproductUr a (u: Initial 𝐂): coproduct a u a a (init u a).
Proof. exact:(productUr (u:=obop u)). Defined.

Lemma coproductUl a (u: Initial 𝐂): coproduct u a a (init u a) a.
Proof. exact:(productUl (u:=obop u)). Defined.

Lemma coproductA a b c (ab: Coproduct a b) (bc: Coproduct b c) (x: Coproduct ab c):
  coproduct a bc x (in1\;in1) (copair (in2\;in1) in2).
Proof. exact:(productA (ab:=obop ab) (bc:=obop bc) (obop x)). Defined.

Lemma coproductA' a b c (ab: Coproduct a b) (bc: Coproduct b c) (x: Coproduct a bc):
  coproduct ab c x (copair in1 (in1 \; in2)) (in2 \; in2).
Proof. exact:(productA' (ab:=obop ab) (bc:=obop bc) (obop x)). Defined.
  
End s.

(** ** categories with initial objects / binary coproducts / finite coproducts *)
#[primitive] HB.mixin Record Has0 𝐂 of QUIVER 𝐂 := {
    #[canonical=no] zero: Initial 𝐂;
}.
#[short(type="Cat0")]
HB.structure Definition CAT0 := { 𝐂 of CAT 𝐂 & Has0 𝐂}.

HB.instance Definition _ (𝐂: Cat1) :=
  Has0.Build (𝐂^op) (obop one).
HB.instance Definition _ (𝐂: Cat0) :=
  Has1.Build (𝐂^op) (obop zero).


#[primitive] HB.mixin Record HasBinaryCoproducts 𝐂 of PRECAT 𝐂 := {
    #[canonical=no] coprod: forall a b: ob 𝐂, Coproduct a b;
}.

#[short(type="CatBCoprod")]
HB.structure Definition CATBCOPROD := { 𝐂 of CAT 𝐂 & HasBinaryCoproducts 𝐂}.
Infix "+" := coprod: cat_scope.

#[short(type="CatCoprod")]
HB.structure Definition CATCOPROD := { 𝐂 of CAT0 𝐂 & CATBCOPROD 𝐂}.


HB.instance Definition _ (𝐂: CatBProd) :=
  HasBinaryCoproducts.Build (𝐂^op) (fun a b => obop (prod a b)).
HB.instance Definition _ (𝐂: CatBCoprod) :=
  HasBinaryProducts.Build (𝐂^op) (fun a b => obop (coprod a b)).
HB.saturate op. 

Section s.
Context {𝐂: CatBCoprod}.
Implicit Types a b c d: ob 𝐂.

Definition coprodP a b: coproduct a b (a+b) in1 in2 := coproductP. 

(** [hcoprod] for "coprod" on homsets *)
Definition hcoprod a b c d (f: a~>c) (g: b~>d): a+b ~> c+d := hprod (morphop f) (morphop g).

#[export] Instance coprod_eqv {a b c d}: Proper (eqv ==> eqv ==> eqv) (@hcoprod a b c d).
Proof. exact: (@prod_eqv 𝐂^op). Qed. 

Lemma coprod_id a b: hcoprod a b ≡ idmap.
Proof. exact: (@prod_id 𝐂^op). Qed.

Lemma coprod_comp a a' a'' b b' b'' (f: a~>a') (f': a'~>a'') (g: b~>b') (g': b'~>b''):
  hcoprod (f\;f') (g\;g') ≡ hcoprod f g \; hcoprod f' g'.
Proof. exact: (@prod_comp 𝐂^op). Qed.

Lemma coprod1 a b c d (f: a~>c) (g: b~>d): in1 \; hcoprod f g ≡ f \; in1.
Proof. exact: (@prod1 𝐂^op). Qed.

Lemma coprod2 a b c d (f: a~>c) (g: b~>d): in2 \; hcoprod f g ≡ g \; in2.
Proof. exact: (@prod2 𝐂^op). Qed.

Lemma coprodE a b c d (f: a~>c) (g: b~>d): in1 \; hcoprod f g ≡ f \; in1 ∧ in2 \; hcoprod f g ≡ g \; in2.
Proof. exact: (@prodE 𝐂^op). Qed.

(** [hcoprod] preserves epis (but not monos)
    as a functor, it also preserves split epis, split monos, and isomorphisms *)

Lemma coprod_epi a a' b b' (f: Epi a a') (g: Epi b b'): is_epi (hcoprod f g).
Proof. exact: (prod_mono (f:=morphop f) (g:=morphop g)). Qed.
HB.instance Definition _ a a' b b' (f: Epi a a') (g: Epi b b') :=
  IsEpi.Build _ _ _ (hcoprod f g) (@coprod_epi _ _ _ _ f g).

HB.instance Definition _ a a' b b' (f: Invertible a a') (g: Invertible b b') :=
  HasInverseOp.Build _ _ _ (hcoprod f g) (hcoprod f⁻¹ g⁻¹). 

Lemma coprod_splitmono a a' b b' (f: SplitMono a a') (g: SplitMono b b'): has_right_inverse (hcoprod f g).
Proof. exact: (prod_splitepi (morphop f) (morphop g)). Qed.

HB.instance Definition _ a a' b b' (f: SplitMono a a') (g: SplitMono b b') :=
  HasRightInverse.Build _ _ _ (hcoprod f g) (@coprod_splitmono _ _ _ _ f g).

Lemma coprod_splitepi a a' b b' (f: SplitEpi a a') (g: SplitEpi b b'): has_left_inverse (hcoprod f g).
Proof. exact: (prod_splitmono (morphop f) (morphop g)). Qed.

HB.instance Definition _ a a' b b' (f: SplitEpi a a') (g: SplitEpi b b') :=
  HasLeftInverse.Build _ _ _ (hcoprod f g) (@coprod_splitepi _ _ _ _ f g).

HB.saturate hcoprod.
Definition coprod_iso a a' b b' (f: a ≃ a') (g: b ≃ b'): a+b ≃ a'+b' := hcoprod f g.

(* local notation, consistent with the subsequent notation in (cocartesian) monoidal categories *)
Infix "·" := hcoprod: cat_scope.

(* Note: could be defined already in PreCatBCoprod *)
Definition codiag a: a+a ~> a := copair a a.

Definition coprodC a b: a+b ≃ b+a :=
  CoproductU (CoproductC _) _.

Definition coprodCH a b: cospanhom _ _ _ _ (coprodC a b)¹ :=
  CoproductUH (CoproductC _) _.

Lemma coprodC1 a b: in1 \; coprodC a b ≡ in2.
Proof. apply coprodCH. Qed.

Lemma coprodC2 a b: in2 \; coprodC a b ≡ in1.
Proof. apply coprodCH. Qed.

Lemma coprodC_nat a b a' b' f g: g · f \; coprodC b' a' ≡ coprodC a b \; f · g.
Proof. symmetry. exact/(@prodC_nat 𝐂^op). Qed.

Lemma coprodC_inv a b: (coprodC a b)⁻¹ ≡ coprodC b a.
Proof. done. Qed.

Definition coprodA a b c: (a+b)+c ≃ a+(b+c) :=
  CoproductU (mk_coproduct_ (coproductA _)) _.

Definition coprodAH a b c: cospanhom _ _ _ _ (coprodA a b c)¹ :=
  CoproductUH (mk_coproduct_ (coproductA _)) _.

Lemma coprodA1 a b c: in1 \; in1 \; coprodA a b c ≡ in1.
Proof.
  rewrite -compoA iso_tgt. symmetry.
  exact/(prodA1 (obop a) (obop b) (obop c)).
Qed.

Lemma coprodA2 a b c: in2 \; in1 \; coprodA a b c ≡ in1 \; in2.
Proof.
  rewrite -compoA iso_tgt. symmetry.
  exact/(prodA2 (obop a) (obop b) (obop c)).
Qed.

Lemma coprodA3 a b c: in2 \; coprodA a b c ≡ in2 \; in2.
Proof.
  rewrite iso_tgt. symmetry.
  exact/(prodA3 (obop a) (obop b) (obop c)).
Qed.

Lemma coprodA_nat a b c a' b' c' f g h:
  (f · g) · h \; coprodA a' b' c' ≡ coprodA a b c \; f · (g · h).
Proof.
  rewrite iso_tgt compoA iso_src.
  exact/(prodA_nat (morphop f) (morphop g) (morphop h)).
Qed.

Lemma coprodA_pentagon a b c d:
  coprodA a b c · d \; coprodA a (b + c) d \; a · coprodA b c d ≡ coprodA (a + b) c d \; coprodA a b (c + d).
(* TOFIX: super long to typecheck :( *)
Proof. exact/inv_inj/(prodA_pentagon (obop a) (obop b) (obop c) (obop d)). Qed.

End s.

Section s.
Context {𝐂: CatCoprod}.
Implicit Types a b c d: ob 𝐂.
Infix "·" := hcoprod: cat_scope.

Definition coprodUl a: zero+a ≃ a :=
  CoproductU _ (mk_coproduct_ (@coproductUl _ _ _)).

Definition coprodUlH a: cospanhom _ _ _ _ (coprodUl a)¹ :=
  CoproductUH _ (mk_coproduct_ (@coproductUl _ _ _)).

Lemma coprodUl'2 a: in2 \; coprodUl a ≡ idmap.
Proof. exact/(prodUl'2 (obop a)). Qed.

Lemma coprodUl_in2 a: (coprodUl a)⁻¹ ≡ in2.
Proof. exact/(prodUl_pi2 (obop a)). Qed.

Lemma coprodUl_nat a a' f: idmap · f \; coprodUl a' ≡ coprodUl a \; f.
Proof.
  rewrite iso_tgt compoA iso_src.
  exact/(prodUl_nat (morphop f)). 
Qed.

Definition coprodUr a: a+zero ≃ a :=
  CoproductU _ (mk_coproduct_ (@coproductUr _ _ _)).

Definition coprodUrH a: cospanhom _ _ _ _ (coprodUr a)¹ :=
  CoproductUH _ (mk_coproduct_ (@coproductUr _ _ _)).

(* to be deduced from monoidal symmetry? *)
Lemma coprodUr'1 a: in1 \; coprodUr a ≡ idmap.
Proof. exact/(prodUr'1 (obop a)). Qed.

Lemma coprodUr_in1 a: (coprodUr a)⁻¹ ≡ in1.
Proof. exact/(prodUr_pi1 (obop a)). Qed.

Lemma coprodUr_nat a a' f: f · idmap \; coprodUr a' ≡ coprodUr a \; f.
Proof.
  rewrite iso_tgt compoA iso_src.
  exact/(prodUr_nat (morphop f)). 
Qed.

Lemma coprodA_triangle a b: coprodA a zero b \; a · coprodUl b ≡ coprodUr a · b.
(* TOFIX: super long to typecheck :( *)
Proof. exact/inv_inj/(prodA_triangle (obop a) (obop b)). Qed.

End s.
