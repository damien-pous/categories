(** * casting operation for homsets *)

Require Import cat.

Local Open Scope cat_scope.

(** casting morphism-like types *)
Definition cast2' {A} {T: A -> A -> Type} [a b a' b'] (x: T a b) (aa: a = a') (bb: b = b'): T a' b' :=
  eq_rect _ (fun a => T a b') (eq_rect _ _ x _ bb) _ aa.
Arguments cast2' {_ _} [_ _ _ _] _ & !_ !_.
Notation cast2 a' b' f := (@cast2' _ _ _ _ a' b' f _ _).


(** casting homomorphisms (in quivers) *)
Definition hcast {𝐂: Quiver} A B A' B' a b (f: A ~> B): A' ~> B' :=
  @cast2' _ (@hom 𝐂) A B A' B' f a b.
Arguments hcast {_ _ _ _ _ !_ !_} _.
Notation hcast' f i j := (@hcast _ _ _ _ _ i j f) (only parsing).

(** casting isomorphisms *)
Definition icast {𝐂: PreCat} A B A' B' a b (f: A ≃ B): A' ≃ B' :=
  @cast2' _ (@Iso 𝐂) A B A' B' f a b.
Arguments icast {_ _ _ _ _ !_ !_} _.
Notation icast' f i j := (@icast _ _ _ _ _ i j f) (only parsing).

Section s.
  
Context {𝐂: PreCat}.
Implicit Types A B C D: 𝐂.

(* already for cast2' *)
Lemma hcastI A A' A'' B B' B'' (f: A ~> B)
  (a1: A=A') (a2: A'=A'') (b1: B=B') (b2: B'=B''):
  hcast' (hcast' f a1 b1) a2 b2 =
    hcast' f (etrans a1 a2) (etrans b1 b2).
Proof. by destruct a2; destruct b2. Qed.

(* already for cast2' on setoids *)
#[export] Instance hcast_eqv {A A' B B'} {a: A=A'} {b: B=B'}: Proper (eqv ==> eqv) (@hcast _ _ _ _ _ a b).
Proof. by destruct a; destruct b. Qed.
Lemma hcast_inj A A' B B' (a: A=A') (b: B=B') (f g: A ~> B):
  hcast' f a b ≡ hcast' g a b -> f ≡ g.
Proof. by destruct a; destruct b. Qed.

Lemma hcast_id A A' (e: A=A'): hcast' (idmap A) e e = idmap A'.
Proof. by destruct e. Qed.
Lemma hcast_comp A A' B B' C C' (f: A ~> B) (g: B ~> C) (a: A=A') (b: B=B') (c: C=C'):
  hcast' f a b \; hcast' g b c = hcast' (f \; g) a c.
Proof. by destruct a; destruct b; destruct c. Qed.
Lemma hcast_inv A A' B B' (f: A ≃ B) (a: A=A') (b: B=B'):
  hcast' f⁻¹ b a = (icast' f a b)⁻¹.
Proof. by destruct a; destruct b. Qed.
Lemma hcast_iso A A' B B' (f: A ≃ B) (a: A=A') (b: B=B'):
  hcast' f a b = icast' f a b.
Proof. by destruct a; destruct b. Qed.

(* already for cast2' *)
Lemma icastI A A' A'' B B' B'' (f: A ≃ B)
  (a1: A=A') (a2: A'=A'') (b1: B=B') (b2: B'=B''):
  icast' (icast' f a1 b1) a2 b2 =
    icast' f (etrans a1 a2) (etrans b1 b2).
Proof. by destruct a2; destruct b2. Qed.

(* already for cast2' on setoids *)
HB.instance Definition _ A B := Setoid.copy (A ≃ B) (kernel (@iso.sort _ A B)).
#[export] Instance icast_eqv {A A' B B'} {a: A=A'} {b: B=B'}: Proper (eqv ==> eqv) (@icast _ _ _ _ _ a b).
Proof. by destruct a; destruct b. Qed.
Lemma icast_inj A A' B B' (a: A=A') (b: B=B') (f g: A ≃ B):
  icast' f a b ≡ icast' g a b -> f ≡ g.
Proof. by destruct a; destruct b. Qed.


(** * high level notations *)

(** relaxed composition operation *)
Definition bcomp {A B B' C} (f: A ~> B) (g: B' ~> C) (b: B ≃ B'): A ~> C :=
  locked (g ∘ b ∘ f).

(** casting operation *)
Definition cast A' {A B} B' (f: A ~> B) {i: A' ≃ A} {j: B ≃ B'}: A' ~> B' :=
  locked (j ∘ f ∘ i).

End s. 

Arguments bcomp {_ _ _ _ _} _ _ & {_}, {_ _ _ _ _}.
Arguments cast {_ _ _ _ _} _ & {_ _}, {_} _ {_ _} _ _ {_ _}.
Notation cast' i j f := (@cast _ _ _ _ _ f i j) (only parsing).


Section s.
  
Context {𝐂: Cat}.
Implicit Types A B C D: 𝐂.

Lemma icast_id A A' (e: A=A'): icast' (idmap A) e e = idmap A'.
Proof. by destruct e. Qed.
Lemma icast_comp A A' B B' C C' (f: A ≃ B) (g: B ≃ C) (a: A=A') (b: B=B') (c: C=C'):
  icast' f a b \; icast' g b c = icast' (f \; g) a c.
Proof. by destruct a; destruct b; destruct c. Qed.
Lemma icast_inv A A' B B' (f: A ≃ B) (a: A=A') (b: B=B'):
  icast' f⁻¹ b a = (icast' f a b)⁻¹.
Proof. by destruct a; destruct b. Qed.

Definition blocked_id {A}: A≃A := idmap A.
Definition blocked_comp {A B C} (f: A≃B) (g: B≃C): A≃C := f \; g.
Definition blocked_inv {A B} (f: A≃B): B≃A := f⁻¹.

End s. 

(** class for automatic inferrence of isomorphism equalities (later, for MacLane isomoprhisms) *)

Class auto_eqv {𝐂: PreCat} (A B: 𝐂) (f g: A ≃ B) := aeqv: iso.sort f ≡ g. 

Section s.
  
Context {𝐂: Cat}.
Implicit Types A B C D: 𝐂.

#[export] Instance bcomp_eqv_ {A B B' C}:
  Proper (eqv ==> eqv ==> eqv ==> eqv) (@bcomp _ A B B' C).
Proof. move=>f f' F g g' G m m' M. rewrite /bcomp-!lock. repeat apply: comp_eqv=>//. Qed.
Definition bcomp_eqv {A B B' C f f' g g' m m'} {e: auto_eqv m m'} F G :=
  @bcomp_eqv_ A B B' C f f' F g g' G m m' e.

#[export] Instance cast_eqv_ {A' A B B'}: Proper (eqv==>eqv==>eqv==>eqv) (@cast _ A' A B B').
Proof. move=> f g fg i i' ii j j' jj. rewrite /cast-!lock. repeat apply: comp_eqv=>//. Qed.
Definition cast_eqv {A' A B B' f g i i' j j'} {ii: auto_eqv i i'} {jj: auto_eqv j j'} fg :=
  @cast_eqv_ A' A B B' f g fg i i' ii j j' jj.

Lemma bcompo1 A B C D (f: A ~> B) (m: B ≃ C) (j: C ≃ D):
  bcomp f j m ≡ cast' blocked_id (blocked_comp m j) f.
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma bcomp1o A B C D (i: A ≃ B) (m: B ≃ C) (g: C ~> D):
  bcomp i g m ≡ cast' (blocked_comp i m) blocked_id g.
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma bcompA A B B' C C' D (f: A ~> B) (i: B ≃ B') (g: B' ~> C) (j: C ≃ C') (h: C' ~> D):
  bcomp (bcomp f g i) h j ≡ bcomp f (bcomp g h j) i.
Proof. rewrite /bcomp-!lock. cat. Qed.

Lemma bcompK A B C (f: A ~> B) (m: B ≃ B) (g: B ~> C) {e: auto_eqv m idmap}:
  bcomp f g m ≡ f \; g.
Proof. rewrite /bcomp-lock e/=. cat. Qed.

Lemma castI A'' A'  A B B' B'' f i i' j' j:
  @cast _ A'' A' B' B'' (@cast _ A' A B B' f i j) i' j' ≡
    @cast _ A'' A B B'' f (blocked_comp i' i) (blocked_comp j j').
Proof. rewrite /cast-!lock/=. cat. Qed.

Lemma castK A B (i: A ≃ A) (j: B ≃ B) f {I: auto_eqv i idmap} {J: auto_eqv j idmap}:
  cast' i j f ≡ f.
Proof. rewrite /cast-lock I J/=. cat. Qed.

Lemma castIK A'  A B B' (i i' j' j: _ ≃ _) f {I: auto_eqv (i'\;i) idmap} {J: auto_eqv (j\;j') idmap}:
  @cast _ A A' B' B (@cast _ A' A B B' f i j) i' j' ≡ f.
Proof. rewrite castI. exact: castK. Qed.

Lemma cast_id A' A A'' i j: @cast _ A' A A A'' idmap i j ≡ blocked_comp i j.
Proof. rewrite /cast-!lock/blocked_comp. cat. Qed.

Lemma cast_comp A'  A B D D' (i: A' ≃ A) (k: D ≃ D') (f: A ~> B) (g: B ~> D):
  cast' i k (g ∘ f) ≡ cast' blocked_id k g ∘ cast' i blocked_id f.
Proof. rewrite /cast-!lock/=. cat. Qed.

Lemma cast_bcomp A'  A B B' D D' (i: A' ≃ A) (k: D ≃ D') (m: B ≃ B') (f: A ~> B) (g: B' ~> D):
  cast' i k (bcomp f g m) ≡ cast' m k g ∘ cast' i blocked_id f.
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma cast_bcomp' A'  A B B' D D' (i: A' ≃ A) (k: D ≃ D') (m: B ≃ B') (f: A ~> B) (g: B' ~> D):
  cast' i k (bcomp f g m) ≡ cast' blocked_id k g ∘ cast' i m f.
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma comp_cast A'  A B B' B'' D D' (k: A' ≃ A) (l: B ≃ B'') (j: D ≃ D') (i: B'' ≃ B') (f: A ~> B) (g: B' ~> D):
  cast' i j g ∘ cast' k l f ≡ cast' k j (bcomp f g (blocked_comp l i)).
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma comp_cast_l A B B' D D' (j: D ≃ D') (i: B ≃ B') (f: A ~> B) (g: B' ~> D):
  cast' i j g ∘ f ≡ cast' blocked_id j (bcomp f g i).
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma comp_cast_r A'  A B B' D (k: A' ≃ A) (l: B ≃ B') (f: A ~> B) (g: B' ~> D):
  g ∘ cast' k l f ≡ cast' k blocked_id (bcomp f g l).
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma bcomp_cast A'  A B B' B'' B''' D D' (k: A' ≃ A) (l: B ≃ B'') (j: D ≃ D') (i: B''' ≃ B') m (f: A ~> B) (g: B' ~> D):
  bcomp (cast' k l f) (cast' i j g) m ≡ cast' k j (bcomp f g (blocked_comp l (blocked_comp m i))).
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma bcomp_cast_l A B B' B''' D D' (j: D ≃ D') (i: B''' ≃ B') m (f: A ~> B) (g: B' ~> D):
  bcomp f (cast' i j g) m ≡ cast' blocked_id j (bcomp f g (blocked_comp m i)).
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.

Lemma bcomp_cast_r A'  A B B' B'' D (k: A' ≃ A) (l: B ≃ B'') m (f: A ~> B) (g: B' ~> D):
  bcomp (cast' k l f) g m ≡ cast' k blocked_id (bcomp f g (blocked_comp l m)).
Proof. rewrite /cast/bcomp-!lock/=. cat. Qed.


Lemma cast_switch_ A' A B B' (i: A'≃A) (j: B≃B') f g:
  cast' i j f ≡ g -> f ≡ cast' (blocked_inv i) (blocked_inv j) g.
Proof.
  rewrite /cast-!lock.
  by rewrite iso_src iso_tgt compoA. 
Qed.

Lemma cast_switch A' A B B' (i: A'≃A) (j: B≃B') f g:
  cast' i j f ≡ g <-> f ≡ cast' (blocked_inv i) (blocked_inv j) g.
Proof.
  split. apply: cast_switch_.
  move=>/eqv_sym/cast_switch_ ->. exact/cast_eqv. 
Qed.

Lemma cast_switch' A' A B B' (i: A'≃A) (j: B≃B') f g:
  g ≡ cast' i j f <-> cast' (blocked_inv i) (blocked_inv j) g ≡ f.
Proof. symmetry. exact/cast_switch. Qed.

Lemma cast_eqv_iff A' A B B' (i i': A'≃A) f f' (j j': B≃B') {I: auto_eqv i i'} {J: auto_eqv j j'}:
  cast' i j f ≡ cast' i' j' f' <-> f ≡ f'.
Proof.
  split. 2: move=>?;exact/cast_eqv.
  move=>/cast_switch->.
  apply/cast_switch. apply/cast_eqv=>//; exact/eqv_sym.
Qed.

Lemma eqv_trans_cast A B A' B' (f: A ~> B) (h: A' ~> B') (g: A ~> B) (p q: _ ≃ _):
  f ≡ cast' p q h ->
  h ≡ cast' (blocked_inv p) (blocked_inv q) g ->
  f ≡ g.
Proof. move=>->->. by rewrite cast_switch. Qed.

Lemma eqv_trans_cast' A B A' B' A'' B'' (f: A ~> B) (h: A' ~> B') (g: A'' ~> B'') (i j p q: _ ≃ _):
  f ≡ cast' p q h ->
  h ≡ cast' (blocked_comp (blocked_inv p) i) (blocked_comp j (blocked_inv q)) g ->
  f ≡ cast' i j g.
Proof. move=>->->. by rewrite cast_switch castI. Qed.

End s.
Arguments eqv_trans_cast {_ _ _ _ _} [_] _ [_]&_ _. 
Arguments eqv_trans_cast' {_ _ _ _ _ _ _} [_] _ [_ _ _]&_ _. 

(** * categories with unicity of identity proofs between lists of objects (and thus also objects) *)

#[primitive] HB.mixin Record HasUIP X := {
    #[canonical=no] UIP_ob_list: forall n m: list X,
      forall p q: n = m, p = q;
  }.
#[short(type="UIP")]
HB.structure Definition uip := { X of HasUIP X }.
#[short(type="PreCatUIP")]
HB.structure Definition precat_uip := { 𝐂 of uip 𝐂 & precat 𝐂 }.

Lemma UIP_ob (X: UIP): forall A B: X, forall p q: A = B, p = q.
Proof.
  have L: forall A B: X, forall p: A=B,
      f_equal (fun h => match h with cons B _ => B | _ => A end)
        (f_equal (cons^~ nil) p) = p.
  by destruct p. 
  move=>A B p q.
  rewrite -(L _ _ p) -(L _ _ q). f_equal. exact/UIP_ob_list.
Qed.

Section s.
  
Context {𝐂: PreCatUIP}.
Implicit Types A B C D: 𝐂.

Lemma hcastK A B (f: A ~> B) (a: A=A) (b: B=B): hcast' f a b = f. 
Proof. by rewrite (UIP_ob a erefl) (UIP_ob b erefl). Qed.
Lemma hcast_eqv' A A' B B' (a a': A=A') (b b': B=B') (f g: A ~> B):
  f ≡ g -> hcast' f a b ≡ hcast' g a' b'.
Proof. rewrite (UIP_ob a a') (UIP_ob b b'). exact/hcast_eqv. Qed.
Lemma hcast_inj' A A' B B' (a a': A=A') (b b': B=B') (f g: A ~> B): 
  hcast' f a b ≡ hcast' g a b -> f ≡ g.
Proof. rewrite (UIP_ob a a') (UIP_ob b b'). exact/hcast_inj. Qed.
Lemma hcast_id' A A' (a a': A=A'): hcast' idmap a a' = idmap.
Proof. rewrite (UIP_ob a a'). exact/hcast_id. Qed.
Lemma hcast_comp' A A' B B' C C' (f: A ~> B) (g: B ~> C) (a: A=A') (b b': B=B') (c: C=C'):
  hcast' f a b \; hcast' g b' c = hcast' (f \; g) a c.
Proof. rewrite (UIP_ob b b'). exact/hcast_comp. Qed.

End s. 
