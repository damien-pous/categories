Require Export cat.

Local Open Scope cat_scope.

Definition is_epi (𝐂: PreCat) (A B: 𝐂) (e: A ~> B) := forall C (f g: B ~> C), f ∘ e ≡ g ∘ e -> f ≡ g.
Definition is_mono (𝐂: PreCat) (A B: 𝐂) (m: A ~> B) := forall C (f g: C ~> A), m ∘ f ≡ m ∘ g -> f ≡ g.
Arguments is_epi {_ _ _} _/. 
Arguments is_mono {_ _ _} _/. 

HB.mixin Record IsMono (𝐂: PreCat) (A B: 𝐂) (f: A ~> B) := {
    #[canonical=no] mono_prop: is_mono f;
}.
#[short(type="Mono")]
HB.structure Definition mono 𝐂 A B := { f of IsMono 𝐂 A B f }.
Infix "↪" := Mono: cat_scope.
Arguments mono_prop {_ _ _}.

HB.mixin Record IsEpi (𝐂: PreCat) (A B: 𝐂) (f: A ~> B) := {
    #[canonical=no] epi_prop: is_epi f;
}.
#[short(type="Epi")]
HB.structure Definition epi 𝐂 A B := { f of IsEpi 𝐂 A B f }.
Infix "↠" := Epi: cat_scope. 
Arguments epi_prop {_ _ _}.
                                                       
HB.instance Definition _ (𝐂: PreCat) (A B: 𝐂) (f: A ↪ B) :=
  IsEpi.Build 𝐂^op B A (morphop f) (mono_prop f).
HB.instance Definition _ (𝐂: PreCat) (A B: 𝐂) (f: A ↠ B) :=
  IsMono.Build 𝐂^op B A (morphop f) (epi_prop f).
  
Lemma id_is_epi (𝐂: Cat) (A: 𝐂): is_epi A. 
Proof. move=>B f g. by rewrite !cats. Qed.
Lemma id_is_mono (𝐂: Cat) (A: 𝐂): is_mono A. 
Proof. exact: (@id_is_epi 𝐂^op). Qed.

HB.instance Definition _ (𝐂: Cat) (A: 𝐂) := IsEpi.Build _ _ _ idmap (@id_is_epi _ A). 
HB.instance Definition _ (𝐂: Cat) (A: 𝐂) := IsMono.Build _ _ _ idmap (@id_is_mono _ A). 

Lemma comp_is_epi (𝐂: Cat) (A B C: 𝐂) (f: A ↠ B) (g: B ↠ C): is_epi (f \; g). 
Proof. move=>D i j. rewrite !cats=>H. exact/(epi_prop g)/(epi_prop f). Qed.
Lemma comp_is_mono (𝐂: Cat) (A B C: 𝐂) (f: A ↪ B) (g: B ↪ C): is_mono (f \; g). 
Proof. exact: (@comp_is_epi (𝐂^op) _ _ _ (morphop g) (morphop f)). Qed.

HB.instance Definition _ (𝐂: Cat) (A B C: 𝐂) (f: A ↠ B) (g: B ↠ C) :=
  IsEpi.Build _ _ _ (f \; g) (@comp_is_epi _ _ _ _ f g). 
HB.instance Definition _ (𝐂: Cat) (A B C: 𝐂) (f: A ↪ B) (g: B ↪ C) :=
  IsMono.Build _ _ _ (f \; g) (@comp_is_mono _ _ _ _ f g). 


HB.mixin Record HasInverseOp (𝐂: Quiver) (A B: 𝐂) (f: A ~> B) := {
    #[canonical=no] inv: B ~> A;
}.
#[short(type="Invertible")]
HB.structure Definition invertible 𝐂 A B := { f of HasInverseOp 𝐂 A B f }.
Arguments inv {_ _ _}.
Notation "f ⁻¹" := (inv f): cat_scope.
Notation "f ¹" := (bare f): cat_scope.

HB.instance Definition _ (𝐂: Quiver) (A B: 𝐂) (f: Invertible A B) :=
  HasInverseOp.Build 𝐂 B A (f⁻¹) f. 
HB.instance Definition _ (𝐂: Quiver) (A B: 𝐂) (f: Invertible A B) :=
  HasInverseOp.Build (𝐂^op) B A (morphop f) (f⁻¹). 

HB.instance Definition _ (𝐂: PreCat) (A: 𝐂) :=
  HasInverseOp.Build 𝐂 A A A A. 
HB.instance Definition _ (𝐂: PreCat) (A B C: 𝐂) (f: Invertible A B) (g: Invertible B C) :=
  HasInverseOp.Build 𝐂 A C (f \; g) (g⁻¹ \; f⁻¹). 


Definition has_left_inverse (𝐂: PreCat) (A B: 𝐂) (f: Invertible A B) := f⁻¹ \; f ≡ idmap. 
Definition has_right_inverse (𝐂: PreCat) (A B: 𝐂) (f: Invertible A B) := f \; f⁻¹ ≡ idmap.
Arguments has_left_inverse {_ _ _} _/. 
Arguments has_right_inverse {_ _ _} _/. 

Lemma left_inverse_epi (𝐂: Cat) (A B: 𝐂) (f: Invertible A B): has_left_inverse f -> is_epi f.
Proof. move=>K C i j H. by rewrite -(comp1o i) -K compoA H -compoA K cats. Qed.
Lemma right_inverse_mono (𝐂: Cat) (A B: 𝐂) (f: Invertible A B): has_right_inverse f -> is_mono f.
Proof. exact: (@left_inverse_epi (𝐂^op) _ _ (morphop f)). Qed.

HB.mixin Record _HasLeftInverse (𝐂: PreCat) (A B: 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKl: has_left_inverse f;
  }.
#[short(type="SplitEpi")]
HB.structure Definition splitepi 𝐂 A B := { f of epi _ f & invertible _ f & _HasLeftInverse 𝐂 A B f }.
HB.factory Record HasLeftInverse' (𝐂: Cat) (A B: 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKl: has_left_inverse f;
  }.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of HasLeftInverse' 𝐂 A B f.
HB.instance Definition _ := IsEpi.Build _ _ _ f (left_inverse_epi invKl).
HB.instance Definition _ := _HasLeftInverse.Build _ _ _ f invKl.
HB.end.
HB.factory Record HasLeftInverse (𝐂: Cat) (A B: 𝐂) (f: A ~> B) := {
    g: B ~> A;
    invKl: g \; f ≡ idmap;
  }.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of HasLeftInverse 𝐂 A B f.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f g. 
HB.instance Definition _ := HasLeftInverse'.Build _ _ _ f invKl.
HB.end.

HB.mixin Record _HasRightInverse (𝐂: PreCat) (A B: 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKr: has_right_inverse f;
  }.
#[short(type="SplitMono")]
HB.structure Definition splitmono 𝐂 A B := { f of mono _ f & invertible _ f & _HasRightInverse 𝐂 A B f }.
HB.factory Record HasRightInverse' (𝐂: Cat) (A B: 𝐂) f of HasInverseOp _ A B f := {
    #[canonical=no] invKr: has_right_inverse f;
  }.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of HasRightInverse' 𝐂 A B f.
HB.instance Definition _ := IsMono.Build _ _ _ f (right_inverse_mono invKr).
HB.instance Definition _ := _HasRightInverse.Build _ _ _ f invKr.
HB.end.
HB.factory Record HasRightInverse (𝐂: Cat) (A B: 𝐂) (f: A ~> B) := {
    g: B ~> A;
    invKr: f \; g ≡ idmap;
  }.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of HasRightInverse 𝐂 A B f.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f g. 
HB.instance Definition _ := HasRightInverse'.Build _ _ _ f invKr.
HB.end.

Arguments invKl {_ _ _ _},{_ _ _}.
Arguments invKr {_ _ _ _},{_ _ _}.
#[deprecated(note="use invKl instead")]
Definition isoK := @invKl.
#[deprecated(note="use invKr instead")]
Definition isoK' := @invKr.

HB.instance Definition _ (𝐂: PreCat) (A B: 𝐂) (f: SplitMono A B) :=
  _HasLeftInverse.Build 𝐂^op B A (morphop f) invKr.
HB.instance Definition _ (𝐂: PreCat) (A B: 𝐂) (f: SplitEpi A B) :=
  _HasRightInverse.Build 𝐂^op B A (morphop f) invKl.

HB.instance Definition _ (𝐂: Cat) (A B: 𝐂) (f: SplitMono A B) :=
  HasLeftInverse.Build 𝐂 B A (f⁻¹) invKr.
HB.instance Definition _ (𝐂: Cat) (A B: 𝐂) (f: SplitEpi A B) :=
  HasRightInverse.Build 𝐂 B A (f⁻¹) invKl.

Lemma id_has_left_inverse (𝐂: Cat) (A: 𝐂): has_left_inverse (idmap A).
Proof. by rewrite /= cats. Qed.
Lemma id_has_right_inverse (𝐂: Cat) (A: 𝐂): has_right_inverse (idmap A).
Proof. exact: (@id_has_left_inverse (𝐂^op)). Qed.

HB.instance Definition _ (𝐂: Cat) (A: 𝐂) :=
  _HasLeftInverse.Build _ _ _ idmap (id_has_left_inverse A). 
HB.instance Definition _ (𝐂: Cat) (A: 𝐂) :=
  _HasRightInverse.Build _ _ _ idmap (id_has_right_inverse A). 

Lemma comp_has_left_inverse (𝐂: Cat) (A B C: 𝐂) (f: SplitEpi A B) (g: SplitEpi B C): has_left_inverse (f \; g). 
Proof. by rewrite /= compoA -(compoA _ _ g) invKl cats invKl. Qed.
Lemma comp_has_right_inverse (𝐂: Cat) (A B C: 𝐂) (f: SplitMono A B) (g: SplitMono B C): has_right_inverse (f \; g). 
Proof. exact: (@comp_has_left_inverse (𝐂^op) _ _ _ (morphop g) (morphop f)). Qed.

HB.instance Definition _ (𝐂: Cat) (A B C: 𝐂) (f: SplitEpi A B) (g: SplitEpi B C) :=
  _HasLeftInverse.Build _ _ _ (f \; g) (comp_has_left_inverse f g). 
HB.instance Definition _ (𝐂: Cat) (A B C: 𝐂) (f: SplitMono A B) (g: SplitMono B C) :=
  _HasRightInverse.Build _ _ _ (f \; g) (comp_has_right_inverse f g). 


#[short(type="Iso")]
  HB.structure Definition iso (𝐂: PreCat) (A B: 𝐂) := { f of @splitepi 𝐂 A B f & splitmono _ f }.
Infix "≃" := Iso: cat_scope.
Notation "A ≃_ 𝐂 B" := (@Iso 𝐂 A B) (only parsing): cat_scope.

HB.factory Record IsIso' (𝐂: Cat) (A B: 𝐂) f of HasInverseOp _ A B f := {
    invKl: has_left_inverse f;
    invKr: has_right_inverse f;
  }.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of IsIso' 𝐂 A B f.
HB.instance Definition _ := HasLeftInverse.Build _ _ _ f invKl.
HB.instance Definition _ := HasRightInverse.Build _ _ _ f invKr.
HB.end.

HB.factory Record IsIso (𝐂: Cat) (A B: 𝐂) (f: A ~> B) := {
    g: B ~> A;
    invKl: g \; f ≡ idmap;
    invKr: f \; g ≡ idmap;
  }.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of IsIso 𝐂 A B f.
HB.instance Definition _ := HasInverseOp.Build _ _ _ f g.
HB.instance Definition _ := IsIso'.Build _ _ _ f invKl invKr.
HB.end.


HB.saturate idmap.
HB.saturate comp.
HB.saturate inv.
(* TOREPORT: following line should equip [morphop] with a canonical Iso structure *)
(* HB.saturate morphop. *)
(* asymmetric & strange workaround below *)
HB.instance Definition _ (𝐂: PreCat) (A B: 𝐂) (i: A ≃ B) :=
  _HasLeftInverse.Build (𝐂^op) B A (morphop i) invKr.


Lemma epiP {𝐂: Cat} {A B: 𝐂} (e: A ↠ B) C (f g: B ~> C): e \; f ≡ e \; g <-> f ≡ g.
Proof. split. exact/epi_prop. exact/comp_eqv. Qed.
Lemma monoP {𝐂: Cat} {A B: 𝐂} (m: A ↪ B) C (f g: C ~> A): f \; m ≡ g \; m <-> f ≡ g.
Proof. exact: (@epiP (𝐂^op) _ _ (morphop m)). Qed.

Lemma epi_compK {𝐂: Cat} {A B C: 𝐂} (f: A ~> B) (g: B ~> C): is_epi (f \; g) -> is_epi g.
Proof. move=>E D i j H. apply/E. by rewrite !cats H. Qed.
Lemma mono_compK {𝐂: Cat} {A B C: 𝐂} (f: A ~> B) (g: B ~> C): is_mono (f \; g) -> is_mono f.
Proof. exact: (@epi_compK (𝐂^op) _ _ _ (morphop g) (morphop f)). Qed.


Lemma split_epi_mono {𝐂: Cat} {A B: 𝐂} (f: SplitEpi A B): is_mono f -> has_right_inverse f.
Proof. move=>M/=. apply/M. rewrite compoA invKl. cat. Qed.
Lemma split_mono_epi {𝐂: Cat} {A B: 𝐂} (f: SplitMono A B): is_epi f -> has_left_inverse f.
Proof. exact: (@split_epi_mono (𝐂^op) _ _ (morphop f)). Qed.

HB.factory Record SplitEpi_Mono_isIso (𝐂: Cat) (A B: 𝐂) f of @splitepi _ A B f & mono _ f := {}.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of SplitEpi_Mono_isIso 𝐂 A B f.
HB.instance Definition _ := _HasRightInverse.Build _ _ _ f (split_epi_mono (mono_prop f)).
HB.end.

HB.factory Record SplitMono_Epi_isIso (𝐂: Cat) (A B: 𝐂) f of @splitmono _ A B f & epi _ f := {}.
HB.builders Context (𝐂: Cat) (A B: 𝐂) f of SplitMono_Epi_isIso 𝐂 A B f.
HB.instance Definition _ := _HasLeftInverse.Build _ _ _ f (split_mono_epi (epi_prop f)).
HB.end.

Section s.
Context {𝐂: Cat}.
Implicit Types A B C: 𝐂.

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

Lemma iso_tgt_r {𝐂: Cat} (A B B': 𝐂) (f: A ~> B) (g: A ~> B') (i: B' ≃ B): f ≡ i ∘ g <-> i⁻¹ ∘ f  ≡ g.
Proof. exact: (@iso_src_r (𝐂^op) _ _ _ f g (morphop i)). Qed.
Lemma iso_tgt_l {𝐂: Cat} (A B B': 𝐂) (f: A ~> B) (g: A ~> B') (i: B ≃ B'): f \; i ≡ g <-> f  ≡ g \; i⁻¹.
Proof. exact: (@iso_src_l (𝐂^op) _ _ _ f g (morphop i)). Qed.
Definition iso_tgt := (@iso_tgt_l, @iso_tgt_r)%core.

(** forging isomorphisms from scratch (TODO: same for other concepts) *)
Definition mk_iso {𝐂: Cat} {A B: 𝐂} (i: A ~> B) (j: B ~> A) (_: j \; i ≡ idmap) (_: i \; j ≡ idmap) := i.
Arguments mk_iso {_ _ _}. 
HB.instance Definition _ 𝐂 A B i j ji ij := @IsIso.Build 𝐂 A B (@mk_iso 𝐂 A B i j ji ij) j ji ij. 
Definition mk_iso' {𝐂: Cat} {A B: 𝐂} (i: A ~> B) (j: B ~> A) ji ij: A ≃ B := mk_iso i j ji ij. 
Arguments mk_iso' {_ _ _}.

(** isomorphisms in product categories *)
Program Definition pair_iso {𝐂 𝐃: Cat} {A A' B B'} (i: A ≃_𝐂 A') (j: B ≃_𝐃 B'): (A,B) ≃ (A',B')
  := @mk_iso (𝐂*𝐃)%type (A,B) (A',B') (i¹,j¹) (i⁻¹, j⁻¹)  _ _.
Next Obligation. split; exact: invKl. Qed.
Next Obligation. split; exact: invKr. Qed.
