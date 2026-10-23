(** hierarchy of morphisms: (split/regular) {mono,epi}morphisms and isomorphisms *)

Require Import cat.
Require Import arewrite.

Open Scope cat_scope.

(** * epi/mono *)

Definition is_epi (𝐂: PreCat) (A B: ob 𝐂) (e: A ~> B) := forall C (f g: B ~> C), f ∘ e ≡ g ∘ e -> f ≡ g.
Definition is_mono (𝐂: PreCat) (A B: ob 𝐂) (m: A ~> B) := forall C (f g: C ~> A), m ∘ f ≡ m ∘ g -> f ≡ g.
Arguments is_epi {_ _ _} _/. 
Arguments is_mono {_ _ _} _/. 

HB.mixin Record IsEpi (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] epiP: is_epi f;
}.
#[short(type="Epi")]
HB.structure Definition EPI 𝐂 A B := { f of IsEpi 𝐂 A B f }.
Infix "↠" := Epi: cat_scope. 
Arguments epiP {_ _ _}.
HB.instance Definition _ 𝐂 A B := Setoid.copy (@Epi 𝐂 A B) (kernel (@EPI.sort 𝐂 A B)).

HB.mixin Record IsMono (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] monoP: is_mono f;
}.
#[short(type="Mono")]
HB.structure Definition MONO 𝐂 A B := { f of IsMono 𝐂 A B f }.
Infix "↪" := Mono: cat_scope.
Arguments monoP {_ _ _}.
HB.instance Definition _ 𝐂 A B := Setoid.copy (@Mono 𝐂 A B) (kernel (@MONO.sort 𝐂 A B)).

HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: A ↪ B) :=
  IsEpi.Build 𝐂^op B A (morphop f) (monoP f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂^op) (f: A ↪ B) :=
  IsEpi.Build 𝐂 B A (morphop' f) (monoP f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: A ↠ B) :=
  IsMono.Build 𝐂^op B A (morphop f) (epiP f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂^op) (f: A ↠ B) :=
  IsMono.Build 𝐂 B A (morphop' f) (epiP f).

Lemma id_is_epi (𝐂: Cat) (A: ob 𝐂): is_epi A. 
Proof. move=>B f g. by rewrite !cats. Qed.
Lemma id_is_mono (𝐂: Cat) (A: ob 𝐂): is_mono A. 
Proof. exact: (id_is_epi (A:=obop A)). Qed.

HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := IsEpi.Build _ _ _ idmap (@id_is_epi _ A). 
HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := IsMono.Build _ _ _ idmap (@id_is_mono _ A). 

Lemma comp_is_epi (𝐂: Cat) (A B C: ob 𝐂) (f: A ↠ B) (g: B ↠ C): is_epi (f \; g). 
Proof. move=>D i j. rewrite !cats=>H. exact/(epiP g)/(epiP f). Qed.
Lemma comp_is_mono (𝐂: Cat) (A B C: ob 𝐂) (f: A ↪ B) (g: B ↪ C): is_mono (f \; g). 
Proof. exact: (comp_is_epi (f:=morphop g) (g:=morphop f)). Qed.

HB.instance Definition _ (𝐂: Cat) (A B C: ob 𝐂) (f: A ↠ B) (g: B ↠ C) :=
  IsEpi.Build _ _ _ (f \; g) (@comp_is_epi _ _ _ _ f g). 
HB.instance Definition _ (𝐂: Cat) (A B C: ob 𝐂) (f: A ↪ B) (g: B ↪ C) :=
  IsMono.Build _ _ _ (f \; g) (@comp_is_mono _ _ _ _ f g). 

(** * regular epi/mono *)

(** we define them here because they have to be inserted in the hierarchy
    between epi/mono and split epi/mono
    however, their definition rests on (co)equalizer, which are to be studied later as (co)limits
    thus we postpone the elaboration of their theory
 *)

Definition is_equalizer (𝐂: PreCat) (A B C: ob 𝐂) (f g: A ~> B) (e: C ~> A) :=
  e \; f ≡ e \; g ∧ forall D (e': D ~> A), e' \; f ≡ e' \; g -> Σ! h: D ~> C, h \; e ≡ e'.
Definition is_coequalizer (𝐂: PreCat) (A B C: ob 𝐂) (f g: A ~> B) (e: B ~> C) :=
  f \; e ≡ g \; e ∧ forall D (e': B ~> D), f \; e' ≡ g \; e' -> Σ! h: C ~> D, e \; h ≡ e'.

Definition is_regepi (𝐂: PreCat) (A B: ob 𝐂) (e: A ~> B) :=
  { C & {f: C~>A & {g: C~>A & is_coequalizer f g e }}}.
Definition is_regmono (𝐂: PreCat) (A B: ob 𝐂) (m: A ~> B) :=
  { C & {f: B~>C & {g: B~>C & is_equalizer f g m }}}.
Arguments is_regepi {_ _ _} _/.
Arguments is_regmono {_ _ _} _/.

HB.mixin Record _IsRegEpi (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] regepiP: is_regepi f;
}.
#[short(type="RegEpi")]
HB.structure Definition REGEPI 𝐂 A B := { f of _IsRegEpi 𝐂 A B f & EPI _ f }.
Arguments regepiP {_ _ _}.
(** [is_regepi] quantifies on objects and return a Type,
    so that regular epis live in a universe which is at least that of objects, wich must be strictly above that of setoids since we want the category of setoids
    thus we cannot declare a setoid structure on regepis (and regmonos, and isos) until we get universe polymorphic setoids
 *)
HB.instance Definition _ 𝐂 A B := Setoid.copy (@RegEpi 𝐂 A B) (kernel (@REGEPI.sort 𝐂 A B)).

HB.mixin Record _IsRegMono (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] regmonoP: is_regmono f;
}.
#[short(type="RegMono")]
HB.structure Definition REGMONO 𝐂 A B := { f of _IsRegMono 𝐂 A B f & MONO _ f }.
Arguments regmonoP {_ _ _}.
HB.instance Definition _ 𝐂 A B := Setoid.copy (@RegMono 𝐂 A B) (kernel (@REGMONO.sort 𝐂 A B)).

HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: RegMono A B) :=
  _IsRegEpi.Build 𝐂^op B A (morphop f) (regmonoP f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂^op) (f: RegMono A B) :=
  _IsRegEpi.Build 𝐂 B A (morphop' f) (regmonoP f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: RegEpi A B) :=
  _IsRegMono.Build 𝐂^op B A (morphop f) (regepiP f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂^op) (f: RegEpi A B) :=
  _IsRegMono.Build 𝐂 B A (morphop' f) (regepiP f).

Lemma regepi_epi (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B): is_regepi f -> is_epi f.
Proof.
  move=>[D [a [b [P U]]]] C i j H.
  apply: unicity_sig. apply: U. all: cbn. 2: exact: H. 2: done.
  arewrite P; cat. 
Qed.
Lemma regmono_mono (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B): is_regmono f -> is_mono f.
Proof. exact: (regepi_epi (f:=morphop f)). Qed.

HB.factory Record IsRegEpi (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := {
    regepiP: is_regepi f;
}.
HB.builders Context 𝐂 A B f of IsRegEpi 𝐂 A B f.
HB.instance Definition _ := IsEpi.Build _ _ _ f (regepi_epi regepiP).
HB.instance Definition _ := _IsRegEpi.Build _ _ _ f regepiP.
HB.end.

HB.factory Record IsRegMono (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := {
    regmonoP: is_regmono f;
}.
HB.builders Context 𝐂 A B f of IsRegMono 𝐂 A B f.
HB.instance Definition _ := IsMono.Build _ _ _ f (regmono_mono regmonoP).
HB.instance Definition _ := _IsRegMono.Build _ _ _ f regmonoP.
HB.end.

  
Lemma id_is_regepi (𝐂: Cat) (A: ob 𝐂): is_regepi A. 
Proof.
  exists A, idmap, idmap. split=>//.
  move=>D e' _. apply mk_unique_sig with e'. cat.
  move=>h. rewrite cats. exact/eqv_sym. 
Qed.
Lemma id_is_regmono (𝐂: Cat) (A: ob 𝐂): is_regmono A. 
Proof. exact: (id_is_regepi (obop A)). Qed.

HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := _IsRegEpi.Build _ _ _ idmap (@id_is_regepi _ A). 
HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := _IsRegMono.Build _ _ _ idmap (@id_is_regmono _ A). 

(* regular epi/mono are not closed under composition in arbitrary categories *)


(** * morphisms with an unspecified inverse *)

HB.mixin Record HasInverseOp (𝐂: BareQuiver) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] inv: B ~> A;
}.
#[short(type="Invertible")]
HB.structure Definition INVERTIBLE 𝐂 A B := { f of HasInverseOp 𝐂 A B f }.
Arguments inv {_ _ _}.
Notation "f ⁻¹" := (inv f): cat_scope.

HB.instance Definition _ (𝐂: BareQuiver) (A B: ob 𝐂) (f: Invertible A B) :=
  HasInverseOp.Build 𝐂 B A (f⁻¹) f. 
HB.instance Definition _ (𝐂: BareQuiver) (A B: ob 𝐂) (f: Invertible A B) :=
  HasInverseOp.Build 𝐂^op B A (morphop f) (f⁻¹). 
HB.instance Definition _ (𝐂: BareQuiver) (A B: ob 𝐂^op) (f: Invertible A B) :=
  HasInverseOp.Build 𝐂 B A (morphop' f) (f⁻¹). 

HB.instance Definition _ (𝐂: BarePreCat) (A: ob 𝐂) :=
  HasInverseOp.Build 𝐂 A A A A. 
HB.instance Definition _ (𝐂: BarePreCat) (A B C: ob 𝐂) (f: Invertible A B) (g: Invertible B C) :=
  HasInverseOp.Build 𝐂 A C (f \; g) (g⁻¹ \; f⁻¹). 



(** * split epi/mono, i.e., morphisms with left/right inverses *)

Definition has_left_inverse (𝐂: PreCat) (A B: ob 𝐂) (f: Invertible A B) := f⁻¹ \; f ≡ idmap. 
Definition has_right_inverse (𝐂: PreCat) (A B: ob 𝐂) (f: Invertible A B) := f \; f⁻¹ ≡ idmap.
Arguments has_left_inverse {_ _ _} _/. 
Arguments has_right_inverse {_ _ _} _/. 

(* subsumed by the regular versions below *)
Lemma left_inverse_epi (𝐂: Cat) (A B: ob 𝐂) (f: Invertible A B): has_left_inverse f -> is_epi f.
Proof. move=>K C i j H. rewrite -(comp1o i) -K. arewrite H. arewrite K. cat. Qed.
Lemma right_inverse_mono (𝐂: Cat) (A B: ob 𝐂) (f: Invertible A B): has_right_inverse f -> is_mono f.
Proof. exact: (left_inverse_epi (f:=morphop f)). Qed.

Lemma left_inverse_regepi (𝐂: Cat) (A B: ob 𝐂) (f: Invertible A B): has_left_inverse f -> is_regepi f.
Proof.
  move=>K. exists A, (f\;f⁻¹), idmap. split. arewrite K. cat.
  move=>D e H. apply mk_unique_sig with (f⁻¹\;e). arewrite H. cat.
  move=>h <-. arewrite K. cat.
Qed.
Lemma right_inverse_regmono (𝐂: Cat) (A B: ob 𝐂) (f: Invertible A B): has_right_inverse f -> is_regmono f.
Proof. exact: (left_inverse_regepi (f:=morphop f)). Qed.

HB.mixin Record _HasLeftInverse (𝐂: PreCat) (A B: ob 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKl: has_left_inverse f;
  }.
#[short(type="SplitEpi")]
HB.structure Definition SPLITEPI 𝐂 A B := { f of REGEPI _ f & INVERTIBLE _ f & _HasLeftInverse 𝐂 A B f }.
HB.instance Definition _ 𝐂 A B := Setoid.copy (SplitEpi A B) (kernel (@SPLITEPI.sort 𝐂  A B)).
HB.factory Record HasLeftInverse' (𝐂: Cat) (A B: ob 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKl: has_left_inverse f;
  }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of HasLeftInverse' 𝐂 A B f.
HB.instance Definition _ := IsRegEpi.Build _ _ _ f (left_inverse_regepi invKl).
HB.instance Definition _ := _HasLeftInverse.Build _ _ _ f invKl.
HB.end.
HB.factory Record HasLeftInverse (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := {
    g: B ~> A;
    invKl: g \; f ≡ idmap;
  }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of HasLeftInverse 𝐂 A B f.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f g. 
HB.instance Definition _ := HasLeftInverse'.Build _ _ _ f invKl.
HB.end.

HB.mixin Record _HasRightInverse (𝐂: PreCat) (A B: ob 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKr: has_right_inverse f;
  }.
#[short(type="SplitMono")]
HB.structure Definition SPLITMONO 𝐂 A B := { f of REGMONO _ f & INVERTIBLE _ f & _HasRightInverse 𝐂 A B f }.
HB.instance Definition _ 𝐂 A B := Setoid.copy (SplitMono A B) (kernel (@SPLITMONO.sort 𝐂 A B)).
HB.factory Record HasRightInverse' (𝐂: Cat) (A B: ob 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKr: has_right_inverse f;
  }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of HasRightInverse' 𝐂 A B f.
HB.instance Definition _ := IsRegMono.Build _ _ _ f (right_inverse_regmono invKr).
HB.instance Definition _ := _HasRightInverse.Build _ _ _ f invKr.
HB.end.
HB.factory Record HasRightInverse (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := {
    g: B ~> A;
    invKr: f \; g ≡ idmap;
  }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of HasRightInverse 𝐂 A B f.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f g. 
HB.instance Definition _ := HasRightInverse'.Build _ _ _ f invKr.
HB.end.

Arguments invKl {_ _ _ _},{_ _ _}.
Arguments invKr {_ _ _ _},{_ _ _}.
#[deprecated(note="use invKl instead")]
Definition isoK := @invKl.
#[deprecated(note="use invKr instead")]
Definition isoK' := @invKr.

HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: SplitMono A B) :=
  _HasLeftInverse.Build 𝐂^op B A (morphop f) invKr.
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂^op) (f: SplitMono A B) :=
  _HasLeftInverse.Build 𝐂 B A (morphop' f) (invKr (s:=f)).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: SplitEpi A B) :=
  _HasRightInverse.Build 𝐂^op B A (morphop f) invKl.
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂^op) (f: SplitEpi A B) :=
  _HasRightInverse.Build 𝐂 B A (morphop' f) (invKl (s:=f)).

HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) (f: SplitMono A B) :=
  HasLeftInverse.Build 𝐂 B A (f⁻¹) invKr.
HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) (f: SplitEpi A B) :=
  HasRightInverse.Build 𝐂 B A (f⁻¹) invKl.

Lemma id_has_left_inverse (𝐂: Cat) (A: ob 𝐂): has_left_inverse (idmap A).
Proof. by rewrite /= cats. Qed.
Lemma id_has_right_inverse (𝐂: Cat) (A: ob 𝐂): has_right_inverse (idmap A).
Proof. exact: (id_has_left_inverse (obop A)). Qed.

HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) :=
  _HasLeftInverse.Build _ _ _ idmap (id_has_left_inverse A). 
HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) :=
  _HasRightInverse.Build _ _ _ idmap (id_has_right_inverse A). 

Lemma comp_has_left_inverse (𝐂: Cat) (A B C: ob 𝐂) (f: SplitEpi A B) (g: SplitEpi B C): has_left_inverse (f \; g). 
Proof. rewrite /=/inv/=. arewrite invKl. exact/invKl. Qed.
Lemma comp_has_right_inverse (𝐂: Cat) (A B C: ob 𝐂) (f: SplitMono A B) (g: SplitMono B C): has_right_inverse (f \; g). 
Proof. exact: (comp_has_left_inverse (morphop g) (morphop f)). Qed.

HB.instance Definition _ (𝐂: Cat) (A B C: ob 𝐂) (f: SplitEpi A B) (g: SplitEpi B C) :=
  HasLeftInverse.Build _ _ _ (f \; g) (comp_has_left_inverse f g). 
HB.instance Definition _ (𝐂: Cat) (A B C: ob 𝐂) (f: SplitMono A B) (g: SplitMono B C) :=
  HasRightInverse.Build _ _ _ (f \; g) (comp_has_right_inverse f g). 

(** * isomorphisms *)

Definition is_iso (𝐂: PreCat) (a b: ob 𝐂) (f: a ~> b) (g: b ~> a) :=
  g \; f ≡ idmap ∧ f \; g ≡ idmap.

#[short(type="Iso")]
  HB.structure Definition ISO (𝐂: PreCat) (A B: ob 𝐂) := { f of @SPLITEPI 𝐂 A B f & SPLITMONO _ f }.
Arguments Iso {_}.
Infix "≃" := Iso: cat_scope.
Notation "A ≃_ 𝐂 B" := (@Iso 𝐂 A B) (only parsing): cat_scope.
Notation "f ¹" := (ISO.sort f): cat_scope.
HB.instance Definition _ 𝐂 A B := Setoid.copy (A ≃ B) (kernel (@ISO.sort 𝐂 A B)).

Lemma isoP (𝐂: PreCat) (a b: ob 𝐂) (i: a ≃ b): is_iso i i⁻¹.
Proof. split. exact/invKl. exact/invKr. Qed.

HB.factory Record IsIso' (𝐂: Cat) (A B: ob 𝐂) f of @INVERTIBLE _ A B f := 
  { isoP: is_iso f (inv f) }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of IsIso' 𝐂 A B f.
HB.instance Definition _ := HasLeftInverse.Build _ _ _ f isoP.1.
HB.instance Definition _ := HasRightInverse.Build _ _ _ f isoP.2.
HB.end.

HB.factory Record IsIso (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := 
  { g: B ~> A; isoP: is_iso f g }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of IsIso 𝐂 A B f.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f g.
HB.instance Definition _ := IsIso'.Build _ _ _ f isoP.
HB.end.

HB.saturate idmap.
HB.saturate comp.
HB.saturate inv.
HB.saturate morphop.
(* Check fun (C: Cat) (a b: C) (i: a≃b) => morphop i: _ ≃ _. *)

(** * additional properties *)

Lemma isoC (𝐂: PreCat) (a b: ob 𝐂) (f: a ~> b) (g: b ~> a):
  is_iso f g -> is_iso g f.
Proof. exact: swap_pair. Qed.

Lemma epiP' {𝐂: Cat} {A B: ob 𝐂} (e: A ↠ B) C (f g: B ~> C): e \; f ≡ e \; g <-> f ≡ g.
Proof. split. exact/epiP. exact/comp_eqv. Qed.
Lemma monoP' {𝐂: Cat} {A B: ob 𝐂} (m: A ↪ B) C (f g: C ~> A): f \; m ≡ g \; m <-> f ≡ g.
Proof. exact: (epiP' (morphop m)). Qed.

Lemma epi_compK {𝐂: Cat} {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C): is_epi (f \; g) -> is_epi g.
Proof. move=>E D i j H. apply/E. by rewrite !cats H. Qed.
Lemma mono_compK {𝐂: Cat} {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C): is_mono (f \; g) -> is_mono f.
Proof. exact: (epi_compK (f:=morphop g) (g:=morphop f)). Qed.


(* subsumed by the regular version below *)
Lemma splitepi_mono_right_inverse {𝐂: Cat} {A B: ob 𝐂} (f: SplitEpi A B): is_mono f -> has_right_inverse f.
Proof. move=>M/=. apply/M. arewrite invKl. cat. Qed.
Lemma splitmono_epi_left_inverse {𝐂: Cat} {A B: ob 𝐂} (f: SplitMono A B): is_epi f -> has_left_inverse f.
Proof. exact: (splitepi_mono_right_inverse (f:=morphop f)). Qed.

HB.factory Record SplitEpi_Mono_isIso (𝐂: Cat) (A B: ob 𝐂) f of @SPLITEPI _ A B f & MONO _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of SplitEpi_Mono_isIso 𝐂 A B f.
HB.instance Definition _ := HasRightInverse.Build _ _ _ f (splitepi_mono_right_inverse (monoP f)).
HB.end.

HB.factory Record SplitMono_Epi_isIso (𝐂: Cat) (A B: ob 𝐂) f of @SPLITMONO _ A B f & EPI _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of SplitMono_Epi_isIso 𝐂 A B f.
HB.instance Definition _ := HasLeftInverse.Build _ _ _ f (splitmono_epi_left_inverse (epiP f)).
HB.end.


Lemma regepi_mono_right_inverse {𝐂: Cat} {A B: ob 𝐂} (f: RegEpi A B): is_mono f -> { g & f \; g ≡ idmap }.
Proof.
  move=>M/=. move: (regepiP f)=>[C [i [j [P U]]]].
  apply: (U _ idmap _).1. by rewrite 2!cats; apply M in P.
Qed.
Lemma regmono_epi_left_inverse {𝐂: Cat} {A B: ob 𝐂} (f: RegMono A B): is_epi f -> { g & g \; f ≡ idmap }.
Proof. exact: (regepi_mono_right_inverse (f:=morphop f)). Qed.

HB.factory Record RegEpi_Mono_isIso (𝐂: Cat) (A B: ob 𝐂) f of @REGEPI _ A B f & MONO _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of RegEpi_Mono_isIso 𝐂 A B f.
Definition regepi_mono_inv := projT1 (regepi_mono_right_inverse (monoP f)).
Opaque regepi_mono_inv.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f regepi_mono_inv.
HB.instance Definition _ := HasRightInverse.Build _ _ _ f (projT2 (regepi_mono_right_inverse (monoP f))).
HB.end.

HB.factory Record RegMono_Epi_isIso (𝐂: Cat) (A B: ob 𝐂) f of @REGMONO _ A B f & EPI _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of RegMono_Epi_isIso 𝐂 A B f.
Definition regmono_epi_inv := projT1 (regmono_epi_left_inverse (epiP f)).
Opaque regmono_epi_inv.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f regmono_epi_inv.
HB.instance Definition _ := HasLeftInverse.Build _ _ _ f (projT2 (regmono_epi_left_inverse (epiP f))).
HB.end.



Section s.
Context {𝐂: Cat}.
Implicit Types A B C: ob 𝐂.

Definition iso_refl A: A ≃ A := idmap.
Definition iso_trans A B C (i: A ≃ B) (j: B ≃ C): A ≃ C := j ∘ i.
Definition iso_sym A B (i: A ≃ B): B ≃ A := i⁻¹. 

Lemma invI A B (i: A ≃ B): i⁻¹⁻¹ ≡ i.
Proof. done. Qed.
Lemma inv_id A: (idmap A)⁻¹ ≡ idmap.
Proof. done. Qed.
Lemma inv_comp A B C (i: A ≃ B) (j: B ≃ C): (j∘i)⁻¹ ≡ i⁻¹∘j⁻¹.
Proof. done. Qed.

Lemma iso_src_r A A' B (f: A ~> B) (g: A' ~> B) (i: A ≃ A'): f ≡ i \; g <-> i⁻¹ \; f ≡ g.
Proof. by rewrite -(epiP' i) -compoA invKr cats. Qed.

Lemma iso_src_l A A' B (f: A ~> B) (g: A' ~> B) (i: A' ≃ A): i \; f ≡ g <-> f ≡ i⁻¹ \; g.
Proof. split=>H; exact/eqv_sym/iso_src_r/eqv_sym. Qed.

Lemma inv_eqv A B (i j: A ≃ B): i¹ ≡ j¹ -> i⁻¹ ≡ j⁻¹.
Proof. move=>ij. apply/(epiP i). by rewrite /= invKr ij invKr. Qed.

Lemma inv_inj A B (i j: A ≃ B): i⁻¹ ≡ j⁻¹ -> i¹ ≡ j¹.
Proof. by move=>/inv_eqv. Qed.

Lemma iso_id A: is_iso A A.
Proof. split; cat. Qed.

End s.
Definition iso_src := (@iso_src_l, @iso_src_r)%core.

Lemma iso_tgt_r {𝐂: Cat} (A B B': ob 𝐂) (f: A ~> B) (g: A ~> B') (i: B' ≃ B): f ≡ i ∘ g <-> i⁻¹ ∘ f  ≡ g.
Proof. exact: (iso_src_r _ _ (morphop i)). Qed.
Lemma iso_tgt_l {𝐂: Cat} (A B B': ob 𝐂) (f: A ~> B) (g: A ~> B') (i: B ≃ B'): f \; i ≡ g <-> f  ≡ g \; i⁻¹.
Proof. exact: (iso_src_l _ _ (morphop i)). Qed.
Definition iso_tgt := (@iso_tgt_l, @iso_tgt_r)%core.

(** forging isomorphisms from scratch (TODO: same for other concepts) *)
Definition iso {𝐂: Cat} {A B: ob 𝐂} (i: A ~> B) (j: B ~> A) (_: is_iso i j) := i.
Arguments iso {_ _ _} _ _ _/. 
HB.instance Definition _ 𝐂 A B i j ij := @IsIso.Build 𝐂 A B (@iso 𝐂 A B i j ij) j ij. 
Definition iso_ {𝐂: Cat} {A B: ob 𝐂} (i: A ~> B) (j: B ~> A) ij: A ≃ B := iso i j ij. 
Arguments iso_ {_ _ _} _ _/.

(** isomorphisms in product categories *)
Program Definition pair_iso {𝐂 𝐃: Cat} {A A' B B'} (i: A ≃_𝐂 A') (j: B ≃_𝐃 B'): (A,B) ≃ (A',B')
  := @iso_ (𝐂*𝐃)%type (A,B) (A',B') (i,j) (i⁻¹, j⁻¹)  _.
Next Obligation. split. split; exact: invKl. split; exact: invKr. Qed.
Arguments pair_iso {_ _ _ _ _ _} _ _/.


(**  unicity of initial/terminal objects, up to (unique) isomorphism *)
Program Definition InitialU {𝐂: Cat} (a b: Initial 𝐂): a ≃ b :=
  iso_ (init _ _) (init _ _) _.
Next Obligation. split; exact/initU. Qed. 
Arguments InitialU {_} _ _/.

Program Definition TerminalU {𝐂: Cat} (a b: Terminal 𝐂): a ≃ b :=
  iso_ (term _ _) (term _ _) _.
Next Obligation. split; exact/termU. Qed. 
Arguments TerminalU {_} _ _/.
