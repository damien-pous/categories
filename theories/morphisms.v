(** hierarchy of morphisms: (split/regular) {mono,epi}morphisms and isomorphisms *)

Require Export cat.
Require Import arewrite.

Local Open Scope cat_scope.

(** * epi/mono *)

Definition is_epi (𝐂: PreCat) (A B: ob 𝐂) (e: A ~> B) := forall C (f g: B ~> C), f ∘ e ≡ g ∘ e -> f ≡ g.
Definition is_mono (𝐂: PreCat) (A B: ob 𝐂) (m: A ~> B) := forall C (f g: C ~> A), m ∘ f ≡ m ∘ g -> f ≡ g.
Arguments is_epi {_ _ _} _/. 
Arguments is_mono {_ _ _} _/. 

HB.mixin Record IsEpi (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] epi_prop: is_epi f;
}.
#[short(type="Epi")]
HB.structure Definition epi 𝐂 A B := { f of IsEpi 𝐂 A B f }.
Infix "↠" := Epi: cat_scope. 
Arguments epi_prop {_ _ _}.

HB.mixin Record IsMono (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] mono_prop: is_mono f;
}.
#[short(type="Mono")]
HB.structure Definition mono 𝐂 A B := { f of IsMono 𝐂 A B f }.
Infix "↪" := Mono: cat_scope.
Arguments mono_prop {_ _ _}.

HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: A ↪ B) :=
  IsEpi.Build 𝐂^op B A (morphop f) (mono_prop f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: A ↠ B) :=
  IsMono.Build 𝐂^op B A (morphop f) (epi_prop f).

Lemma id_is_epi (𝐂: Cat) (A: ob 𝐂): is_epi A. 
Proof. move=>B f g. by rewrite !cats. Qed.
Lemma id_is_mono (𝐂: Cat) (A: ob 𝐂): is_mono A. 
Proof. exact: (id_is_epi (A:=obop A)). Qed.

HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := IsEpi.Build _ _ _ idmap (@id_is_epi _ A). 
HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := IsMono.Build _ _ _ idmap (@id_is_mono _ A). 

Lemma comp_is_epi (𝐂: Cat) (A B C: ob 𝐂) (f: A ↠ B) (g: B ↠ C): is_epi (f \; g). 
Proof. move=>D i j. rewrite !cats=>H. exact/(epi_prop g)/(epi_prop f). Qed.
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
  prod (e \; f ≡ e \; g) (forall D (e': D ~> A), e' \; f ≡ e' \; g -> Σ! h: D ~> C, h \; e ≡ e').  
Definition is_coequalizer (𝐂: PreCat) (A B C: ob 𝐂) (f g: A ~> B) (e: B ~> C) :=
  prod (f \; e ≡ g \; e) (forall D (e': B ~> D), f \; e' ≡ g \; e' -> Σ! h: C ~> D, e \; h ≡ e').  

Definition is_regepi (𝐂: PreCat) (A B: ob 𝐂) (e: A ~> B) :=
  { C & {f: C~>A & {g: C~>A & is_coequalizer f g e }}}.
Definition is_regmono (𝐂: PreCat) (A B: ob 𝐂) (m: A ~> B) :=
  { C & {f: B~>C & {g: B~>C & is_equalizer f g m }}}.

HB.mixin Record _IsRegEpi (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] regepi_prop: is_regepi f;
}.
#[short(type="RegEpi")]
HB.structure Definition regepi 𝐂 A B := { f of _IsRegEpi 𝐂 A B f & epi _ f }.
Arguments regepi_prop {_ _ _}.

HB.mixin Record _IsRegMono (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] regmono_prop: is_regmono f;
}.
#[short(type="RegMono")]
HB.structure Definition regmono 𝐂 A B := { f of _IsRegMono 𝐂 A B f & mono _ f }.
Arguments regmono_prop {_ _ _}.
                                                       
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: RegMono A B) :=
  _IsRegEpi.Build 𝐂^op B A (morphop f) (regmono_prop f).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: RegEpi A B) :=
  _IsRegMono.Build 𝐂^op B A (morphop f) (regepi_prop f).

Lemma regepi_epi (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B): is_regepi f -> is_epi f.
Proof.
  move=>[D [a [b [P U]]]] C i j H.
  apply: Unicity. apply: U. all: cbn. 2: exact: H. 2: done.
  arewrite P; cat. 
Qed.
Lemma regmono_mono (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B): is_regmono f -> is_mono f.
Proof. exact: (regepi_epi (f:=morphop f)). Qed.

HB.factory Record IsRegEpi (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := {
    regepi_prop: is_regepi f;
}.
HB.builders Context 𝐂 A B f of IsRegEpi 𝐂 A B f.
HB.instance Definition _ := IsEpi.Build _ _ _ f (regepi_epi regepi_prop).
HB.instance Definition _ := _IsRegEpi.Build _ _ _ f regepi_prop.
HB.end.

HB.factory Record IsRegMono (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := {
    regmono_prop: is_regmono f;
}.
HB.builders Context 𝐂 A B f of IsRegMono 𝐂 A B f.
HB.instance Definition _ := IsMono.Build _ _ _ f (regmono_mono regmono_prop).
HB.instance Definition _ := _IsRegMono.Build _ _ _ f regmono_prop.
HB.end.

  
Lemma id_is_regepi (𝐂: Cat) (A: ob 𝐂): is_regepi A. 
Proof.
  exists A, idmap, idmap. split=>//.
  move=>D e' _. exists e'. cat.
  move=>h. rewrite cats. exact/eqv_sym. 
Qed.
Lemma id_is_regmono (𝐂: Cat) (A: ob 𝐂): is_regmono A. 
Proof. exact: (id_is_regepi (obop A)). Qed.

HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := _IsRegEpi.Build _ _ _ idmap (@id_is_regepi _ A). 
HB.instance Definition _ (𝐂: Cat) (A: ob 𝐂) := _IsRegMono.Build _ _ _ idmap (@id_is_regmono _ A). 

(* regular epi/mono are not closed under composition in arbitrary categories *)


(** * morphisms with an unspecified inverse *)

(* TOFIX: could be defined in [Quiver], but breaks [airewrite/aireflexivity] tactics for now *)
HB.mixin Record HasInverseOp (𝐂: PreCat) (A B: ob 𝐂) (f: A ~> B) := {
    #[canonical=no] inv: B ~> A;
}.
#[short(type="Invertible")]
HB.structure Definition invertible 𝐂 A B := { f of HasInverseOp 𝐂 A B f }.
Arguments inv {_ _ _}.
Notation "f ⁻¹" := (inv f): cat_scope.
Notation "f ¹" := (bare f): cat_scope.

(* TOFIX: idem, those two instance should lie [Quiver] *)
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: Invertible A B) :=
  HasInverseOp.Build 𝐂 B A (f⁻¹) f. 
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (f: Invertible A B) :=
  HasInverseOp.Build (𝐂^op) B A (morphop f) (f⁻¹). 

HB.instance Definition _ (𝐂: PreCat) (A: ob 𝐂) :=
  HasInverseOp.Build 𝐂 A A A A. 
HB.instance Definition _ (𝐂: PreCat) (A B C: ob 𝐂) (f: Invertible A B) (g: Invertible B C) :=
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
  move=>D e H. exists (f⁻¹\;e). arewrite H. cat.
  move=>h <-. arewrite K. cat.
Qed.
Lemma right_inverse_regmono (𝐂: Cat) (A B: ob 𝐂) (f: Invertible A B): has_right_inverse f -> is_regmono f.
Proof. exact: (left_inverse_regepi (f:=morphop f)). Qed.

HB.mixin Record _HasLeftInverse (𝐂: PreCat) (A B: ob 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKl: has_left_inverse f;
  }.
#[short(type="SplitEpi")]
HB.structure Definition splitepi 𝐂 A B := { f of regepi _ f & invertible _ f & _HasLeftInverse 𝐂 A B f }.
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
HB.structure Definition splitmono 𝐂 A B := { f of regmono _ f & invertible _ f & _HasRightInverse 𝐂 A B f }.
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

HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) (f: SplitMono A B) :=
  HasLeftInverse.Build 𝐂^op B A (morphop f) invKr.
HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) (f: SplitEpi A B) :=
  HasRightInverse.Build 𝐂^op B A (morphop f) invKl.

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

#[short(type="Iso")]
  HB.structure Definition iso (𝐂: PreCat) (A B: ob 𝐂) := { f of @splitepi 𝐂 A B f & splitmono _ f }.
Infix "≃" := Iso: cat_scope.
Notation "A ≃_ 𝐂 B" := (@Iso 𝐂 A B) (only parsing): cat_scope.

HB.factory Record IsIso' (𝐂: Cat) (A B: ob 𝐂) f of HasInverseOp _ A B f := {
    invKl: has_left_inverse f;
    invKr: has_right_inverse f;
  }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of IsIso' 𝐂 A B f.
HB.instance Definition _ := HasLeftInverse.Build _ _ _ f invKl.
HB.instance Definition _ := HasRightInverse.Build _ _ _ f invKr.
HB.end.

HB.factory Record IsIso (𝐂: Cat) (A B: ob 𝐂) (f: A ~> B) := {
    g: B ~> A;
    invKl: g \; f ≡ idmap;
    invKr: f \; g ≡ idmap;
  }.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of IsIso 𝐂 A B f.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f g.
HB.instance Definition _ := IsIso'.Build _ _ _ f invKl invKr.
HB.end.


HB.saturate idmap.
HB.saturate comp.
HB.saturate inv.
HB.saturate morphop.
(* Check fun (C: Cat) (a b: C) (i: a≃b) => morphop i: _ ≃ _. *)

(** * additional properties *)

Lemma epiP {𝐂: Cat} {A B: ob 𝐂} (e: A ↠ B) C (f g: B ~> C): e \; f ≡ e \; g <-> f ≡ g.
Proof. split. exact/epi_prop. exact/comp_eqv. Qed.
Lemma monoP {𝐂: Cat} {A B: ob 𝐂} (m: A ↪ B) C (f g: C ~> A): f \; m ≡ g \; m <-> f ≡ g.
Proof. exact: (epiP (morphop m)). Qed.

Lemma epi_compK {𝐂: Cat} {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C): is_epi (f \; g) -> is_epi g.
Proof. move=>E D i j H. apply/E. by rewrite !cats H. Qed.
Lemma mono_compK {𝐂: Cat} {A B C: ob 𝐂} (f: A ~> B) (g: B ~> C): is_mono (f \; g) -> is_mono f.
Proof. exact: (epi_compK (f:=morphop g) (g:=morphop f)). Qed.


(* subsumed by the regular version below *)
Lemma splitepi_mono_right_inverse {𝐂: Cat} {A B: ob 𝐂} (f: SplitEpi A B): is_mono f -> has_right_inverse f.
Proof. move=>M/=. apply/M. arewrite invKl. cat. Qed.
Lemma splitmono_epi_left_inverse {𝐂: Cat} {A B: ob 𝐂} (f: SplitMono A B): is_epi f -> has_left_inverse f.
Proof. exact: (splitepi_mono_right_inverse (f:=morphop f)). Qed.

HB.factory Record SplitEpi_Mono_isIso (𝐂: Cat) (A B: ob 𝐂) f of @splitepi _ A B f & mono _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of SplitEpi_Mono_isIso 𝐂 A B f.
HB.instance Definition _ := HasRightInverse.Build _ _ _ f (splitepi_mono_right_inverse (mono_prop f)).
HB.end.

HB.factory Record SplitMono_Epi_isIso (𝐂: Cat) (A B: ob 𝐂) f of @splitmono _ A B f & epi _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of SplitMono_Epi_isIso 𝐂 A B f.
HB.instance Definition _ := HasLeftInverse.Build _ _ _ f (splitmono_epi_left_inverse (epi_prop f)).
HB.end.


Lemma regepi_mono_right_inverse {𝐂: Cat} {A B: ob 𝐂} (f: RegEpi A B): is_mono f -> { g & f \; g ≡ idmap }.
Proof.
  move=>M/=. move: (regepi_prop f)=>[C [i [j [P U]]]].
  destruct (U _ idmap) as [g Pg _]. by rewrite 2!cats; apply M in P.
  by exists g.
Qed.
Lemma regmono_epi_left_inverse {𝐂: Cat} {A B: ob 𝐂} (f: RegMono A B): is_epi f -> { g & g \; f ≡ idmap }.
Proof. exact: (regepi_mono_right_inverse (f:=morphop f)). Qed.

HB.factory Record RegEpi_Mono_isIso (𝐂: Cat) (A B: ob 𝐂) f of @regepi _ A B f & mono _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of RegEpi_Mono_isIso 𝐂 A B f.
Definition regepi_mono_inv := projT1 (regepi_mono_right_inverse (mono_prop f)).
Opaque regepi_mono_inv.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f regepi_mono_inv.
HB.instance Definition _ := HasRightInverse.Build _ _ _ f (projT2 (regepi_mono_right_inverse (mono_prop f))).
HB.end.

HB.factory Record RegMono_Epi_isIso (𝐂: Cat) (A B: ob 𝐂) f of @regmono _ A B f & epi _ f := {}.
HB.builders Context (𝐂: Cat) (A B: ob 𝐂) f of RegMono_Epi_isIso 𝐂 A B f.
Definition regmono_epi_inv := projT1 (regmono_epi_left_inverse (epi_prop f)).
Opaque regmono_epi_inv.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f regmono_epi_inv.
HB.instance Definition _ := HasLeftInverse.Build _ _ _ f (projT2 (regmono_epi_left_inverse (epi_prop f))).
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
Proof. by rewrite -(epiP i) -compoA invKr cats. Qed.

Lemma iso_src_l A A' B (f: A ~> B) (g: A' ~> B) (i: A' ≃ A): i \; f ≡ g <-> f ≡ i⁻¹ \; g.
Proof. split=>H; exact/eqv_sym/iso_src_r/eqv_sym. Qed.

Lemma inv_eqv A B (i j: A ≃ B): i ≡[𝐂 A B] j -> i⁻¹ ≡ j⁻¹.
Proof. move=>ij. apply/(epiP i). by rewrite /= invKr ij invKr. Qed.

Lemma inv_inj A B (i j: A ≃ B): i⁻¹ ≡ j⁻¹ -> i ≡ j.
Proof. by move=>/inv_eqv. Qed.

End s.
Definition iso_src := (@iso_src_l, @iso_src_r)%core.

Lemma iso_tgt_r {𝐂: Cat} (A B B': ob 𝐂) (f: A ~> B) (g: A ~> B') (i: B' ≃ B): f ≡ i ∘ g <-> i⁻¹ ∘ f  ≡ g.
Proof. exact: (iso_src_r _ _ (morphop i)). Qed.
Lemma iso_tgt_l {𝐂: Cat} (A B B': ob 𝐂) (f: A ~> B) (g: A ~> B') (i: B ≃ B'): f \; i ≡ g <-> f  ≡ g \; i⁻¹.
Proof. exact: (iso_src_l _ _ (morphop i)). Qed.
Definition iso_tgt := (@iso_tgt_l, @iso_tgt_r)%core.

(** forging isomorphisms from scratch (TODO: same for other concepts) *)
Definition mk_iso {𝐂: Cat} {A B: ob 𝐂} (i: A ~> B) (j: B ~> A) (_: j \; i ≡ idmap) (_: i \; j ≡ idmap) := i.
Arguments mk_iso {_ _ _}. 
HB.instance Definition _ 𝐂 A B i j ji ij := @IsIso.Build 𝐂 A B (@mk_iso 𝐂 A B i j ji ij) j ji ij. 
Definition mk_iso' {𝐂: Cat} {A B: ob 𝐂} (i: A ~> B) (j: B ~> A) ji ij: A ≃ B := mk_iso i j ji ij. 
Arguments mk_iso' {_ _ _}.

(** isomorphisms in product categories *)
Program Definition pair_iso {𝐂 𝐃: Cat} {A A' B B'} (i: A ≃_𝐂 A') (j: B ≃_𝐃 B'): (A,B) ≃ (A',B')
  := @mk_iso (𝐂*𝐃)%type (A,B) (A',B') (i¹,j¹) (i⁻¹, j⁻¹)  _ _.
Next Obligation. split; exact: invKl. Qed.
Next Obligation. split; exact: invKr. Qed.
