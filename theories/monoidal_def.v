(** * monoidal categories *)

Require Export cat cast functor product.

Local Open Scope cat_scope.

(** ** premonoidal categories (i.e., without coherence) *)

(* we define them in several steps in order to setup notations along the way *)
#[primitive] HB.mixin Record HasMonoidalOps 𝐂 of cat 𝐂 := {
    #[canonical=no] unit: 𝐂;
    #[canonical=no] tensor: Functor (𝐂*𝐂)%type 𝐂;
  }.
#[short(type="MonoidalOpsCat")]
HB.structure Definition monoidalopscat := { 𝐂 of cat 𝐂 & HasMonoidalOps 𝐂 }.

Definition tensor11 {𝐂: MonoidalOpsCat} (A B: 𝐂): 𝐂 := app11 tensor A B.
Infix "⊗" := tensor11: cat_scope.
Definition tensor22 {𝐂: MonoidalOpsCat} {A B C D: 𝐂} (f: A~>B) (g: C~>D): A⊗C ~> B⊗D := app22 tensor f g.
Infix "·" := tensor22: cat_scope.

#[primitive] HB.mixin Record IsPreMonoidal 𝐂 of monoidalopscat 𝐂 := {
    (* w.r.t nlab: https://ncatlab.org/nlab/show/monoidal+category
       assoc = α, unitl = λ, unitr = ρ *)
    #[canonical=no] assoc_: forall A B C: 𝐂, (A⊗B)⊗C ≃ A⊗(B⊗C);
    #[canonical=no] unitl_: forall A: 𝐂, unit⊗A ≃ A;
    #[canonical=no] unitr_: forall A: 𝐂, A⊗unit ≃ A;

    #[canonical=no] ntx_assoc_: forall (A B C A' B' C': 𝐂) f g h,
      assoc_ A' B' C' ∘ (f · g) · h ≡ f · (g · h) ∘ assoc_ A B C;
    #[canonical=no] ntx_unitl_: forall (A A': 𝐂) f,
      unitl_ A' ∘ unit · f ≡ f ∘ unitl_ A ;
    #[canonical=no] ntx_unitr_: forall (A A': 𝐂) f,
      unitr_ A' ∘ f · unit ≡ f ∘ unitr_ A ;
  }.
#[short(type="PreMonoidalCat")]
HB.structure Definition premonoidalcat := { 𝐂 of uip 𝐂 & monoidalopscat 𝐂 & IsPreMonoidal 𝐂 }.

(** extension of the normalisation tactic from cat.v *)

Module HL.
  Export HL.
  Definition r_tens {𝐂 A B C D} := r_sym2 (@tensor22 𝐂 A B C D) _.
End HL.
Canonical HL.r_tens.


(** *** basic theory of premonoidal categories *)

Section s.
  
Context {𝐂: PreMonoidalCat}.
Implicit Types A B C D: 𝐂.

Lemma tensor_id {A B}: idmap A · idmap B ≡ idmap (A⊗B). 
Proof. exact: (@Fidmap _ _ _ (A,B)). Qed.
Lemma id_tensor {A B}: idmap (A⊗B) ≡ idmap A · idmap B. 
Proof. by rewrite tensor_id. Qed.

Lemma exchange {A B C A' B' C'}
  (i: A ~> B) (j: B ~> C)
  (i': A' ~> B') (j': B' ~> C'):
  (j·j') ∘ (i·i') ≡ (j∘i) · (j'∘i').
Proof.
  symmetry. 
  exact: (@Fcomp _ _ _ (A,A') (B,B') (C,C') (i,i') (j,j')). 
Qed.

Lemma tensor_lr {A B A' B'} (i: A ~> B) (j: A' ~> B'): i · j ≡ (idmap·j) ∘ (i·idmap).
Proof. rewrite exchange. cat. Qed.
Lemma tensor_rl {A B A' B'} (i: A ~> B) (j: A' ~> B'): i · j ≡ (i·idmap) ∘ (idmap·j).
Proof. rewrite exchange. cat. Qed.

Lemma tensor_comp_l_tgt {A B C D E} (i: A ~> B) (j: B ~> C) (k: D ~> E):
  (j∘i) · k ≡ (j·k) ∘ (i·idmap).
Proof. rewrite exchange. cat. Qed.
Lemma tensor_comp_l_src {A B C D E} (i: A ~> B) (j: B ~> C) (k: D ~> E):
  (j∘i) · k ≡ (j·idmap) ∘ (i·k).
Proof. rewrite exchange. cat. Qed.
Lemma tensor_comp_r_tgt {A B C D E} (i: A ~> B) (j: B ~> C) (k: D ~> E):
  k · (j∘i) ≡ (k·j) ∘ (idmap·i).
Proof. rewrite exchange. cat. Qed.
Lemma tensor_comp_r_src {A B C D E} (i: A ~> B) (j: B ~> C) (k: D ~> E):
  k · (j∘i) ≡ (idmap·j) ∘ (k·i).
Proof. rewrite exchange. cat. Qed.

#[export] Instance tensor_eqv {A B C D}:
  Proper (eqv ==> eqv ==> eqv) (@tensor22 𝐂 A B C D).
Proof. typeclasses eauto. Qed.

Definition _iso_tens {A A' B B'} (i: A ≃ A') (j: B ≃ B'): IsIso _ (A⊗B) (A'⊗B') (i · j) :=  
  @_functor_iso _ _ tensor (A,B) (A',B') (pair_iso i j). 
HB.instance Definition _ {A A' B B'} (i: A ≃ A') (j: B ≃ B') := _iso_tens i j. 


Definition assoc A B C: (A ⊗ B) ⊗ C ~> A ⊗ (B ⊗ C) := (assoc_ A B C)¹.
Definition unitl A: unit ⊗ A ~> A := (unitl_ A)¹.
Definition unitr A: A ⊗ unit ~> A := (unitr_ A)¹.
Arguments assoc: simpl never.
Arguments unitl: simpl never.
Arguments unitr: simpl never.
HB.instance Definition _ A B C := iso.on (assoc A B C). 
HB.instance Definition _ A := iso.on (unitl A). 
HB.instance Definition _ A := iso.on (unitr A). 

Definition assoc' A B C: A ⊗ (B ⊗ C) ~> (A ⊗ B) ⊗ C := (assoc A B C)⁻¹.
Definition unitl' A: A ~> unit ⊗ A := (unitl A)⁻¹.
Definition unitr' A: A ~> A ⊗ unit := (unitr A)⁻¹.
Arguments assoc': simpl never.
Arguments unitl': simpl never.
Arguments unitr': simpl never.
HB.instance Definition _ A B C := iso.on (assoc' A B C). 
HB.instance Definition _ A := iso.on (unitl' A). 
HB.instance Definition _ A := iso.on (unitr' A). 


Lemma ntx_assoc [A B A' B' A'' B''] (f: A ~> B) (g: A' ~> B') (h: A'' ~> B''):
  assoc _ _ _ ∘ (f · g) · h ≡ f · (g · h) ∘ assoc _ _ _.
Proof. exact: ntx_assoc_. Qed.

Lemma ntx_assoc' [A B A' B' A'' B''] (f: A ~> B) (g: A' ~> B') (h: A'' ~> B''):
  assoc' _ _ _ ∘ f · (g · h) ≡ (f · g) · h ∘ assoc' _ _ _.
Proof. by rewrite iso_tgt_l compoA -iso_src_l ntx_assoc. Qed.

Lemma ntx_unitl [A B] (f: A ~> B): unitl _ ∘ unit · f ≡ f ∘ unitl _.
Proof. exact: ntx_unitl_. Qed.

Lemma ntx_unitl' [A B] (f: A ~> B): unitl' _ ∘ f ≡ unit · f ∘ unitl' _.
Proof. by rewrite iso_tgt_l compoA -iso_src_l ntx_unitl. Qed.

Lemma ntx_unitr [A B] (f: A ~> B): unitr _ ∘ f · unit ≡ f ∘ unitr _.
Proof. exact: ntx_unitr_. Qed.

Lemma ntx_unitr' [A B] (f: A ~> B): unitr' _ ∘ f ≡ f · unit ∘ unitr' _.
Proof. by rewrite iso_tgt_l compoA -iso_src_l ntx_unitr. Qed.



Definition tensor11_eq A A' B B' (a: A=A') (b: B=B'): A⊗B = A'⊗B'.
  by rewrite a b.
Defined.
Lemma tensor11_eq_sym A A' B B' (a: A=A') (b: B=B'):
  tensor11_eq (esym a) (esym b) = esym (tensor11_eq a b).
Proof. by destruct a, b. Qed.
Lemma hcast_tensor A A' B B' C C' D D' (f: A ~> B) (g: C ~> D)
  (a: A=A') (b: B=B') (c: C=C') (d: D=D'):
  hcast' f a b · hcast' g c d = hcast' (f · g) (tensor11_eq a c) (tensor11_eq b d).
Proof. by destruct a; destruct b; destruct c; destruct d. Qed.

Lemma hcast_assoc A A' B B' C C' (a: A=A') (b: B=B') (c: C=C'):
  hcast' (assoc A B C)
    (tensor11_eq (tensor11_eq a b) c)
    (tensor11_eq a (tensor11_eq b c))
  = assoc A' B' C'.
Proof. by destruct a; destruct b; destruct c. Qed.
Lemma hcast_assoc_ A A' B B' C C' p q (a: A=A') (b: B=B') (c: C=C'):
  hcast' (assoc A B C) p q = assoc A' B' C'.
Proof.
  rewrite (UIP_ob p (tensor11_eq (tensor11_eq a b) c)).
  rewrite (UIP_ob q (tensor11_eq a (tensor11_eq b c))).
  exact/hcast_assoc.
Qed.
Lemma hcast_assoc' A A' B B' C C' (a: A=A') (b: B=B') (c: C=C'):
  hcast' (assoc' A B C)
    (tensor11_eq a (tensor11_eq b c))
    (tensor11_eq (tensor11_eq a b) c)
  = assoc' A' B' C'.
Proof. by destruct a; destruct b; destruct c. Qed.
Lemma hcast_assoc'_ A A' B B' C C' p q (a: A=A') (b: B=B') (c: C=C'):
  hcast' (assoc' A B C) p q = assoc' A' B' C'.
Proof.
  rewrite (UIP_ob p (tensor11_eq a (tensor11_eq b c))).
  rewrite (UIP_ob q (tensor11_eq (tensor11_eq a b) c)).
  exact/hcast_assoc'.
Qed.
Lemma hcast_unitl A A' (a: A=A'):
  hcast' (unitl A) (tensor11_eq erefl a) a = unitl A'.
Proof. by destruct a. Qed.
Lemma hcast_unitl_ A A' (a: A=A') p:
  hcast' (unitl A) p a = unitl A'.
Proof.
  rewrite (UIP_ob p (tensor11_eq eq_refl a)).
  exact/hcast_unitl.
Qed.
Lemma hcast_unitl' A A' (a: A=A'):
  hcast' (unitl' A) a (tensor11_eq erefl a) = unitl' A'.
Proof. by destruct a. Qed.
Lemma hcast_unitl'_ A A' (a: A=A') p:
  hcast' (unitl' A) a p = unitl' A'.
Proof.
  rewrite (UIP_ob p (tensor11_eq eq_refl a)).
  exact/hcast_unitl'.
Qed.
Lemma hcast_unitr A A' (a: A=A'):
  hcast' (unitr A) (tensor11_eq a erefl) a = unitr A'.
Proof. by destruct a. Qed.
Lemma hcast_unitr_ A A' (a: A=A') p:
  hcast' (unitr A) p a = unitr A'.
Proof.
  rewrite (UIP_ob p (tensor11_eq a eq_refl)).
  exact/hcast_unitr.
Qed.
Lemma hcast_unitr' A A' (a: A=A'):
  hcast' (unitr' A) a (tensor11_eq a erefl) = unitr' A'.
Proof. by destruct a. Qed.
Lemma hcast_unitr'_ A A' (a: A=A') p:
  hcast' (unitr' A) a p = unitr' A'.
Proof.
  rewrite (UIP_ob p (tensor11_eq a eq_refl)).
  exact/hcast_unitr'.
Qed.

(** * class for automatic inferrence of MacLane isomorphisms  *)

Class Bridge A B := mcl: A ≃ B.
Notation mcl_ b := (@mcl _ _ b) (only parsing).

End s.
Arguments mcl {_ _ _}&{_}, {_ _ _} _.

(** association high-level notations *)
Notation "g ∘∘ f" := (bcomp f g mcl) (at level 40, left associativity, only parsing): cat_scope. 
Notation "g ∘∘ f" := (bcomp f g _) (only printing): cat_scope. 
Notation acast f := (@cast _ _ _ _ _ f mcl mcl) (only parsing).

Section s.
  
Context {𝐂: PreMonoidalCat}.
Implicit Types A B C D: 𝐂.

Definition blocked_tens {A B C D} (f: A≃B) (g: C≃D): _ ≃ _ := f · g.
Definition blocked_assoc {A B C}: _ ≃ _ := assoc A B C.
Definition blocked_assoc' {A B C}: _ ≃ _ := assoc' A B C.
Definition blocked_unitl {A}: _ ≃ _ := unitl A.
Definition blocked_unitl' {A}: _ ≃ _ := unitl' A.
Definition blocked_unitr {A}: _ ≃ _ := unitr A.
Definition blocked_unitr' {A}: _ ≃ _ := unitr' A.

(** temporay resolution, to be overriden in [monoidal_gmaclane]  *)
Local Hint Extern 0 (auto_eqv _ _) => unfold auto_eqv; simpl; cat: typeclass_instances.

Lemma bexchange {A B B_ C A' B' B_' C'}
  (i: A ~> B) (j: B_ ~> C)
  (i': A' ~> B') (j': B_' ~> C') (m n n': _ ≃ _)
  (H: iso.sort m ≡ n·n'):
  bcomp (i·i') (j·j') m ≡ (bcomp i j n) · (bcomp i' j' n').
Proof.
  rewrite /bcomp-!lock H.
  by rewrite 2!exchange. 
Qed.

Lemma tensor_bcomp {A B C D A' B' C' D'}
  (i: A ~> B) m (j: C ~> D)
  (i': A' ~> B') m' (j': C' ~> D'):
  (bcomp i j m) · (bcomp i' j' m') ≡ bcomp (i·i') (j·j') (blocked_tens m m').
Proof. by rewrite /bcomp-!lock -2!exchange. Qed.
Lemma tensor_bcomp_l_tgt {A B B' C D E} (i: A ~> B) m (j: B' ~> C) (k: D ~> E):
  bcomp i j m · k ≡ bcomp (i·idmap) (j·k) (blocked_tens m blocked_id).
Proof. by rewrite -tensor_bcomp bcomp1o castK. Qed.
Lemma tensor_bcomp_l_src {A B B' C D E} (i: A ~> B) m (j: B' ~> C) (k: D ~> E):
  bcomp i j m · k ≡ bcomp (i·k) (j·idmap) (blocked_tens m blocked_id).
Proof. by rewrite -tensor_bcomp bcompo1 castK. Qed.
Lemma tensor_bcomp_r_tgt {A B B' C D E} (i: A ~> B) m (j: B' ~> C) (k: D ~> E):
  k · bcomp i j m ≡ bcomp (idmap·i) (k·j) (blocked_tens blocked_id m).
Proof. by rewrite -tensor_bcomp bcomp1o castK. Qed.
Lemma tensor_bcomp_r_src {A B B' C D E} (i: A ~> B) m (j: B' ~> C) (k: D ~> E):
  k · bcomp i j m ≡ bcomp (k·i) (idmap·j) (blocked_tens blocked_id m).
Proof. by rewrite -tensor_bcomp bcompo1 castK. Qed.

Lemma tensor_cast
  A1'  A1 B1 B1' f1 i1 j1
  A2'  A2 B2 B2' f2 i2 j2:
  @cast _ A1' A1 B1 B1' f1 i1 j1 · @cast _ A2' A2 B2 B2' f2 i2 j2  ≡
    cast' (blocked_tens i1 i2) (blocked_tens j1 j2) (f1·f2).
Proof. by rewrite /cast-!lock -2!exchange. Qed.

Lemma tensor_cast_l
  A1'  A1 B1 B1' f1 i1 j1
  A2 B2 (f2: A2 ~> B2):
  @cast _ A1' A1 B1 B1' f1 i1 j1 · f2  ≡
    cast' (blocked_tens i1 blocked_id) (blocked_tens j1 blocked_id) (f1·f2).
Proof. by rewrite -tensor_cast castK. Qed.
Lemma tensor_cast_r
  A1 B1 (f1: A1 ~> B1)
  A2'  A2 B2 B2' f2 i2 j2:
  f1 · @cast _ A2' A2 B2 B2' f2 i2 j2  ≡
    cast' (blocked_tens blocked_id i2) (blocked_tens blocked_id j2) (f1·f2).
Proof. by rewrite -tensor_cast castK. Qed.

Lemma tensorA A B A' B' A'' B'' (f: A ~> B) (g: A' ~> B') (h: A'' ~> B''):
  (f · g) · h ≡ cast' blocked_assoc blocked_assoc' (f · (g · h)).
Proof.
  rewrite /cast-lock-compoA iso_tgt_r.
  exact/ntx_assoc. 
Qed.

Lemma tensorA' A B A' B' A'' B'' (f: A ~> B) (g: A' ~> B') (h: A'' ~> B''):
  f · (g · h) ≡ cast' blocked_assoc' blocked_assoc ((f · g) · h).
Proof. symmetry. rewrite cast_switch. exact/tensorA. Qed. 

Lemma tensorUl A B (f: A ~> B): unit · f ≡ cast' blocked_unitl blocked_unitl' f.
Proof.
  rewrite /cast-lock-compoA iso_tgt_r.
  exact/ntx_unitl. 
Qed.

Lemma tensorUr A B (f: A ~> B): f · unit ≡ cast' blocked_unitr blocked_unitr' f.
Proof.
  rewrite /cast-lock-compoA iso_tgt_r.
  exact/ntx_unitr. 
Qed.

End s.


(** ** monoidal categories (i.e., with coherence laws) *)

#[primitive] HB.mixin Record IsMonoidal 𝐂 of premonoidalcat 𝐂 := {
    #[canonical=no] pentagon: forall A B C D: 𝐂,
      A · assoc B C D ∘ assoc A (B⊗C) D ∘ assoc A B C · D
      ≡ assoc A B (C⊗D) ∘ assoc (A⊗B) C D;

    #[canonical=no] triangle: forall A B: 𝐂,
      A · unitl B ∘ assoc A unit B
      ≡ unitr A · B;    
  }.
#[short(type="MonoidalCat")]
HB.structure Definition monoidalcat := { 𝐂 of IsMonoidal 𝐂 & }.
