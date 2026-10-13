(** structures on objects *)

Require Export functor.
Require Import arewrite.
From Stdlib Require Import CMorphisms.

Local Open Scope cat_scope.

(** * initial/terminal objects *)

Definition is_initial {𝐂: Quiver} (A: ob 𝐂) :=
  forall X, Σ!_: A~>X, True.
Definition is_terminal {𝐂: Quiver} (A: ob 𝐂) :=
  forall X, Σ!_: X~>A, True.

#[primitive]
HB.mixin Record IsInitial (𝐂: Quiver) (A: ob 𝐂) := {
    #[canonical=no] initial_prop: is_initial A 
  }.
#[short(type="Initial")]
HB.structure Definition initial_ob 𝐂 := { A of IsInitial 𝐂 A }.

#[primitive]
HB.mixin Record IsTerminal (𝐂: Quiver) (A: ob 𝐂) := {
    #[canonical=no] terminal_prop: is_terminal A
  }.
#[short(type="Terminal")]
HB.structure Definition terminal_ob 𝐂 := { A of IsTerminal 𝐂 A }.

(* Check fun (C: Quiver) (A: Initial C) => A: ob C. *)
(* Check fun (C: PreCat) (A: Initial C) => A: ob C. *)
(* Check fun (C: Cat) (A: Initial C) => A: ob C. *)

HB.instance Definition _ (𝐂: Quiver) (A: Initial 𝐂) :=
  IsTerminal.Build 𝐂^op (obop A) (@initial_prop _ A).
HB.instance Definition _ (𝐂: Quiver) (A: Terminal 𝐂) :=
  IsInitial.Build 𝐂^op (obop A) (@terminal_prop _ A).

(* Check fun (C: Quiver) (A: Initial C) => obop A: Terminal (C^op). *)
(* Check fun (C: PreCat) (A: Initial C) => obop A: Terminal (C^op). *)
(* Check fun (C: Cat) (A: Initial C) => obop A: Terminal (C^op). *)

Definition initial (𝐂: Quiver) (A: Initial 𝐂) X: A ~> X := unique_morph (initial_prop X).
Definition terminal (𝐂: Quiver) (A: Terminal 𝐂) X: X ~> A := unique_morph (terminal_prop X).

Lemma initialU (𝐂: Quiver) (A: Initial 𝐂) X (f g: A ~> X): f ≡ g.
Proof. apply: unicity. exact: (initial_prop X). all: done. Qed.
Lemma terminalU (𝐂: Quiver) (A: Terminal 𝐂) X (f g: X ~> A): f ≡ g.
Proof. exact: (initialU (morphop f) (morphop g)). Qed.

Definition iso_Initial (𝐂: Cat) (A B: Initial 𝐂): A ≃ B :=
  mk_iso (initial A B) (initial B A) (initialU _ _) (initialU _ _).
Definition iso_Terminal (𝐂: Cat) (A B: Terminal 𝐂): A ≃ B :=
  mk_iso (terminal B A) (terminal A B) (terminalU _ _) (terminalU _ _).

(* useful? *)
Lemma InitialU (𝐂: PreCat) (A B: Initial 𝐂) (i j: A ≃ B): i¹ ≡ j¹.
Proof. exact: initialU. Qed.
Lemma TerminalU (𝐂: PreCat) (A B: Terminal 𝐂) (i j: A ≃ B): i¹ ≡ j¹.
Proof. exact: terminalU. Qed.

Lemma ladj_initial (𝐂 𝐃: Cat) (F: 𝐂 ⊣ 𝐃) (A: ob 𝐂) (H: is_initial A): is_initial (F A).
Proof.
  move=>X. destruct (H (adj F X)) as [f _ U].
  exists (dn f)=>//g _. specialize (U (up g) I). apply: up_inj. by rewrite up_dn.
Qed.
Lemma radj_terminal (𝐂 𝐃: Cat) (F: 𝐂 ⊢ 𝐃) (A: ob 𝐂) (H: is_terminal A): is_terminal (F A).
Proof. exact: (ladj_initial (funcop F) H). Qed.
Lemma cradj_initial (𝐂 𝐃: Cat) (F: CRightAdjoint 𝐂 𝐃) (A: ob 𝐂) (H: is_initial A): is_terminal (F A).
Proof. exact: (ladj_initial (funcop2 F) H). Qed.
Lemma cladj_terminal (𝐂 𝐃: Cat) (F: CLeftAdjoint 𝐂 𝐃) (A: ob 𝐂) (H: is_terminal A): is_initial (F A).
Proof. exact: (ladj_initial (funcop1 F) H). Qed.
(* TOTHINK: forgetful inheritance wrongly detected?
   (should be fine because this is about two distinct hierarchies:
    - the one for functors (indexed by functions [ob C -> ob D]
    - and the one for objects (indexed by objects [ob C]
    is this the source of confusion? )
 *)
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: 𝐂 ⊣ 𝐃) (A: Initial 𝐂) :=
  IsInitial.Build 𝐃 (F A) (ladj_initial F initial_prop).
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: 𝐂 ⊢ 𝐃) (A: Terminal 𝐂) :=
  IsTerminal.Build 𝐃 (F A) (radj_terminal F terminal_prop).
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: CRightAdjoint 𝐂 𝐃) (A: Initial 𝐂) :=
  IsTerminal.Build 𝐃 (F A) (cradj_initial F initial_prop).
#[non_forgetful_inheritance]
HB.instance Definition _ (𝐂 𝐃: Cat) (F: CLeftAdjoint 𝐂 𝐃) (A: Terminal 𝐂) :=
  IsInitial.Build 𝐃 (F A) (cladj_terminal F terminal_prop).

Check fun (𝐂 𝐃: Cat) (F: 𝐂 ⊢ 𝐃) (A: Terminal 𝐂) => F A: Terminal _.
(* TOFIX: HB does not register the required things...
   use a tag above to adhere to its discipline? *)
Fail Check fun (𝐂 𝐃: Cat) (F: AdjointEquivalence 𝐂 𝐃) (A: Terminal 𝐂) => F A: Terminal _.


(** * (co)spans *)

#[primitive] 
HB.mixin Record IsSpan {𝐂: BareQuiver} (A B X: ob 𝐂) := {
    #[canonical=no] pi1: X ~> A;
    #[canonical=no] pi2: X ~> B;
  }.
#[short(type="Span")]
HB.structure Definition span 𝐂 A B := {X of IsSpan 𝐂 A B X}.  
Arguments pi1 {_ _ _ _}, {_ _ _} _. 
Arguments pi2 {_ _ _ _}, {_ _ _} _.
Definition mk_span 𝐂 A B X (f: X ~> A) (g: X ~> B): @Span 𝐂 A B :=
  HB.pack X (IsSpan.Build _ _ _ _ f g). 

#[primitive] 
HB.mixin Record IsCospan {𝐂: BareQuiver} (A B X: ob 𝐂) := {
    #[canonical=no] in1: A ~> X;
    #[canonical=no] in2: B ~> X;
  }.
#[short(type="Cospan")]
HB.structure Definition cospan 𝐂 A B := {X of IsCospan 𝐂 A B X}.  
Arguments in1 {_ _ _ _}, {_ _ _} _. 
Arguments in2 {_ _ _ _}, {_ _ _} _. 
Definition mk_cospan 𝐂 A B X (f: A ~> X) (g: B ~> X): @Cospan 𝐂 A B :=
  HB.pack X (IsCospan.Build _ _ _ _ f g). 

HB.instance Definition _ 𝐂 A B (X: @Span 𝐂 A B) := IsCospan.Build 𝐂^op (obop A) (obop B) (obop X) pi1 pi2. 
HB.instance Definition _ 𝐂 A B (X: @Cospan 𝐂 A B) := IsSpan.Build 𝐂^op (obop A) (obop B) (obop X) in1 in2. 

#[primitive] 
HB.mixin Record IsSpanHom {𝐂: PreCat} {A B: ob 𝐂} (X Y: Span A B) (f: X ~> Y) := {
    #[canonical=no] span_hom: f \; pi1 ≡ pi1 ∧ f \; pi2 ≡ pi2
  }.
#[short(type="SpanHom")]
HB.structure Definition spanhom 𝐂 A B X Y := {f of IsSpanHom 𝐂 A B X Y f}.  
Arguments span_hom {_ _ _ _ _ _}, {_ _ _ _ _} _.
Definition mk_spanhom {𝐂: PreCat} {A B: ob 𝐂} {X Y: Span A B} (f: X ~> Y) (H: f \; pi1 ≡ pi1 ∧ f \; pi2 ≡ pi2): SpanHom X Y := HB.pack f (@IsSpanHom.Build 𝐂 A B X Y f H). 

#[primitive] 
HB.mixin Record IsCospanHom {𝐂: PreCat} {A B: ob 𝐂} (X Y: Cospan A B) (f: X ~> Y) := {
    #[canonical=no] cospan_hom: in1 \; f ≡ in1 ∧ in2 \; f ≡ in2;
  }.
#[short(type="CospanHom")]
HB.structure Definition cospanhom 𝐂 A B X Y := {f of IsCospanHom 𝐂 A B X Y f}.  
Arguments cospan_hom {_ _ _ _ _ _}, {_ _ _ _ _} _.
Definition mk_cospanhom {𝐂: PreCat} {A B: ob 𝐂} {X Y: Cospan A B} (f: X ~> Y) (H: in1 \; f ≡ in1 ∧ in2 \; f ≡ in2): CospanHom X Y := HB.pack f (@IsCospanHom.Build 𝐂 A B X Y f H). 

HB.instance Definition _ 𝐂 A B X Y (f: @SpanHom 𝐂 A B X Y) :=
  IsCospanHom.Build 𝐂^op (obop A) (obop B) (obop Y) (obop X) (morphop f) span_hom. 
HB.instance Definition _ 𝐂 A B X Y (f: @CospanHom 𝐂 A B X Y) :=
  IsSpanHom.Build 𝐂^op (obop A) (obop B) (obop Y) (obop X) (morphop f) cospan_hom. 

HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (X Y: Span A B) :=
  Setoid.copy (SpanHom X Y) (kernel (@spanhom.sort _ _ _ X Y)).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (X Y: Span A B) :=
  IsQuiver.Build (Span A B) (@SpanHom _ _ _).

HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (X Y: Cospan A B) :=
  Setoid.copy (CospanHom X Y) (kernel (@cospanhom.sort _ _ _ X Y)).
HB.instance Definition _ (𝐂: PreCat) (A B: ob 𝐂) (X Y: Cospan A B) :=
  IsQuiver.Build (Cospan A B) (@CospanHom _ _ _).

Section s.
Context {𝐂: Cat} {A B: ob 𝐂}.
Lemma is_span_hom_id (X: Span A B): IsSpanHom _ _ _ _ _ X.
Proof. split. split; cat. Qed.
HB.instance Definition _ X := is_span_hom_id X.
Definition SpanHom_id X := idmap: SpanHom X X.
Lemma is_span_hom_comp (X Y Z: Span A B) (f: SpanHom X Y) (g: SpanHom Y Z): IsSpanHom _ _ _ _ _ (f \; g).
Proof. split. split; by rewrite compoA 2!span_hom. Qed.
HB.instance Definition _ X Y Z f g := @is_span_hom_comp X Y Z f g.
Definition SpanHom_comp (X Y Z: Span A B) (f: X ~> Y) (g: Y ~> Z) := f \; g: SpanHom X Z.
HB.instance Definition _ := IsPreCat.Build (Span A B) (@SpanHom_id) (@SpanHom_comp).
Lemma _span_cat : IsCat (Span A B).
Proof.
  split; intros.
  - exact/comp1o. 
  - exact/compo1. 
  - exact/compoA.
  - intros??????;exact/comp_eqv. 
Qed.
HB.instance Definition _ := _span_cat.
End s. 

Section s.
Context {𝐂: Cat} {A B: ob 𝐂}.
Lemma is_cospan_hom_id (X: Cospan A B): IsCospanHom _ _ _ _ _ X.
Proof. split. by case: (is_span_hom_id (obop (cospan.sort X))). Qed.
HB.instance Definition _ X := is_cospan_hom_id X.
Definition CospanHom_id X := idmap: CospanHom X X.
Lemma is_cospan_hom_comp (X Y Z: Cospan A B) (f: CospanHom X Y) (g: CospanHom Y Z): IsCospanHom _ _ _ _ _ (f \; g).
Proof. split. by case: (is_span_hom_comp (morphop g) (morphop f)). Qed.
HB.instance Definition _ X Y Z f g := @is_cospan_hom_comp X Y Z f g.
Definition CospanHom_comp (X Y Z: Cospan A B) (f: X ~> Y) (g: Y ~> Z) := f \; g: CospanHom X Z.
HB.instance Definition _ := IsPreCat.Build (Cospan A B) (@CospanHom_id) (@CospanHom_comp).
Lemma _cospan_cat : IsCat (Cospan A B).
Proof. 
  split; intros.
  - exact/comp1o. 
  - exact/compo1. 
  - exact/compoA.
  - intros??????;exact/comp_eqv. 
Qed.
HB.instance Definition _ := _cospan_cat.
End s. 

Check fun {𝐂: Cat} {A B: ob 𝐂} (X Y: Span A B) (f: X ~> Y) => X: ob _. (* Span A B *)
Check fun {𝐂: Cat} {A B: ob 𝐂} (X Y: Span A B) (f: X ~> Y) => X: ob 𝐂.
Check fun {𝐂: Cat} {A B C: ob 𝐂} (X Y: Span A B) (f: X ~> Y) (g: (X: ob 𝐂) ~> C) => X \; g.
Check fun {𝐂: Cat} {A B C: ob 𝐂} (X Y: Span A B) (f: X ~> Y) (g: (X: ob 𝐂) ≃ C) => inv g \; f.
Check fun {𝐂: Cat} {A B C: ob 𝐂} (X Y: Span A B) (f: X ≃ Y) (g: (X: ob 𝐂) ≃ C) => inv g \; f¹.

(* Check fun {𝐂: Cat} {A B: ob 𝐂} => unify ((Span A B)^op: PreCat) (Cospan (obop A) (obop B): PreCat). *)

Module A.

Definition spanop {𝐂: BareQuiver} {A B: ob 𝐂} (X: Span A B): @Cospan (𝐂^op) A B :=
  @mk_cospan 𝐂^op A B X (pi1 X) (pi2 X).
Definition cospanop {𝐂: BareQuiver} {A B: ob 𝐂} (X: Cospan A B): @Span (𝐂^op) A B :=
  @mk_span 𝐂^op A B X (in1 X) (in2 X).

Section s.
  Context {𝐂: PreCat} {A B: ob 𝐂}.
  Definition spanhomop [X Y: Span A B] (f: SpanHom X Y): CospanHom (spanop Y) (spanop X)
    := mk_cospanhom (f:=morphop f) (span_hom f).
  Definition cospanhomop [X Y: Cospan A B] (f: CospanHom X Y): SpanHom (cospanop Y) (cospanop X)
  := mk_spanhom (f:=morphop f) (cospan_hom f).

  HB.instance Definition _ :=
    IsBarePreContravariantFunctor.Build (Span A B) (@Cospan 𝐂^op A B) spanop spanhomop.
  HB.instance Definition _ :=
    IsPreContravariantFunctor'.Build (Span A B) (@Cospan 𝐂^op A B) spanop (fun _ _ _ _ H => H).
  
  HB.instance Definition _ :=
    IsBarePreContravariantFunctor.Build (Cospan A B) (@Span 𝐂^op A B) cospanop cospanhomop.
  HB.instance Definition _ :=
    IsPreContravariantFunctor'.Build (Cospan A B) (@Span 𝐂^op A B) cospanop (fun _ _ _ _ H => H).
End s.
Section s.
  Context {𝐂: Cat} {A B: ob 𝐂}.
  HB.instance Definition _ :=
    IsContravariantFunctor.Build (Span A B) (@Cospan 𝐂^op A B) spanop
      (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).
  HB.instance Definition _ :=
    IsContravariantFunctor.Build (Cospan A B) (@Span 𝐂^op A B) cospanop
      (fun _ => eqv_refl) (fun _ _ _ _ _ => eqv_refl).
  (* HB.instance Definition _ := *)
  (*   IsPreAdjoint.Build (Span A B) (@Cospan 𝐂^op A B) spanop cospanop. *)
  (* HB.instance Definition _ := *)
  (*   IsPreAdjoint.Build (Cospan A B) (@Span 𝐂^op A B) cospanop spanop. *)
End s.
Section s.
  Context {𝐂: Cat} {A B: ob 𝐂}.
  (* ARG: cospanop: C^op -> C^op^op instead of C^op -> C *)
  Fail HB.instance Definition _ :=
    IsPreAdjointCF'.Build (Span A B) (@Cospan 𝐂^op A B) spanop cospanop.
End s.

End A.

Definition Fspan {𝐂 𝐃: BareQuiver} (F: ob 𝐂 -> ob 𝐃) {A B: ob 𝐂} (X: Span A B): ob 𝐃 := F X.
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor 𝐂 𝐃) (A B: ob 𝐂) (X: Span A B) :=
  IsSpan.Build 𝐃 (F A) (F B) (Fspan F X) (Fhom F (pi1 X)) (Fhom F (pi2 X)).
HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor 𝐂 𝐃) (A B: ob 𝐂) (X: Span A B) :=
  IsCospan.Build 𝐃 (F A) (F B) (Fspan F X) (Fhom' F (pi1 X)) (Fhom' F (pi2 X)).

Definition Fspan_hom {𝐂 𝐃: PreCat} (F: BarePreFunctor 𝐂 𝐃) {A B: ob 𝐂} {X Y: Span A B} (f: SpanHom X Y): Fspan F X ~> Fspan F Y := Fhom F f.
Lemma is_span_hom_Fspan {𝐂 𝐃: PreCat} {F: Functor 𝐂 𝐃} {A B: ob 𝐂} (X Y: Span A B) (f: SpanHom X Y):
  IsSpanHom 𝐃 (F A) (F B) (Fspan F X) (Fspan F Y) (Fspan_hom F f).
Proof. split; split; cbn; rewrite -Fcomp; apply: Fhom_eqv; apply (span_hom f). Qed.
HB.instance Definition _ 𝐂 𝐃 F A B X Y f := @is_span_hom_Fspan 𝐂 𝐃 F A B X Y f. 

Definition Fspan_hom' {𝐂 𝐃: PreCat} (F: BarePreContravariantFunctor 𝐂 𝐃) {A B: ob 𝐂} {X Y: Span A B} (f: SpanHom X Y): Fspan F Y ~> Fspan F X := Fhom' F f.
Lemma is_cospan_hom_Fspan' {𝐂 𝐃: PreCat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} (X Y: Span A B) (f: SpanHom X Y):
  IsCospanHom 𝐃 (F A) (F B) (Fspan F Y) (Fspan F X) (Fspan_hom' F f).
Proof. split; split; cbn; rewrite -Fcomp'; apply: Fhom'_eqv; apply (span_hom f). Qed.
HB.instance Definition _ 𝐂 𝐃 F A B X Y f := @is_cospan_hom_Fspan' 𝐂 𝐃 F A B X Y f. 

Definition Fcospan {𝐂 𝐃: BareQuiver} (F: ob 𝐂 -> ob 𝐃) {A B: ob 𝐂} (X: Cospan A B): ob 𝐃 := F X.
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor 𝐂 𝐃) (A B: ob 𝐂) (X: Cospan A B) :=
  IsCospan.Build 𝐃 (F A) (F B) (Fcospan F X) (Fhom F (in1 X)) (Fhom F (in2 X)).
HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor 𝐂 𝐃) (A B: ob 𝐂) (X: Cospan A B) :=
  IsSpan.Build 𝐃 (F A) (F B) (Fcospan F X) (Fhom' F (in1 X)) (Fhom' F (in2 X)).

Definition Fcospan_hom {𝐂 𝐃: PreCat} (F: BarePreFunctor 𝐂 𝐃) {A B: ob 𝐂} {X Y: Cospan A B} (f: CospanHom X Y): Fcospan F X ~> Fcospan F Y := Fhom F f.
Lemma is_cospan_hom_Fcospan {𝐂 𝐃: PreCat} {F: Functor 𝐂 𝐃} {A B: ob 𝐂} (X Y: Cospan A B) (f: CospanHom X Y):
  IsCospanHom 𝐃 (F A) (F B) (Fcospan F X) (Fcospan F Y) (Fcospan_hom F f).
Proof. split; split; cbn; rewrite -Fcomp; apply: Fhom_eqv; apply (cospan_hom f). Qed.
HB.instance Definition _ 𝐂 𝐃 F A B X Y f := @is_cospan_hom_Fcospan 𝐂 𝐃 F A B X Y f. 

Definition Fcospan_hom' {𝐂 𝐃: PreCat} (F: BarePreContravariantFunctor 𝐂 𝐃) {A B: ob 𝐂} {X Y: Cospan A B} (f: CospanHom X Y): Fcospan F Y ~> Fcospan F X := Fhom' F f.
Lemma is_span_hom_Fcospan' {𝐂 𝐃: PreCat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} (X Y: Cospan A B) (f: CospanHom X Y):
  IsSpanHom 𝐃 (F A) (F B) (Fcospan F Y) (Fcospan F X) (Fcospan_hom' F f).
Proof. split; split; cbn; rewrite -Fcomp'; apply: Fhom'_eqv; apply (cospan_hom f). Qed.
HB.instance Definition _ 𝐂 𝐃 F A B X Y f := @is_span_hom_Fcospan' 𝐂 𝐃 F A B X Y f. 

Definition Fspan_ {𝐂 𝐃} (F: BarePreContravariantFunctor 𝐂 𝐃) {A B: ob 𝐂} (X: Span A B): Cospan (F A) (F B) := Fspan F X.
HB.instance Definition _ {𝐂 𝐃: PreCat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} :=
  IsBarePreContravariantFunctor.Build (Span A B) (Cospan (F A) (F B)) (Fspan_ F)
    (fun X Y f => Fspan_hom' F f: CospanHom _ _).
HB.instance Definition _ {𝐂 𝐃: PreCat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} :=
  IsPreContravariantFunctor'.Build (Span A B) (Cospan (F A) (F B)) (Fspan_ F) (fun _ _ _ _ H => @Fhom'_eqv _ _ F _ _ _ _ H).
HB.instance Definition _ {𝐂 𝐃: Cat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} :=
  IsContravariantFunctor.Build (Span A B) (Cospan (F A) (F B)) (Fspan_ F) (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _).

Definition Fspan' {𝐂 𝐃} (F: PreAdjointCF 𝐂 𝐃) {A B: ob 𝐂} (X: Cospan (F A) (F B)): ob 𝐂 := adj F X.
HB.instance Definition _ (𝐂 𝐃: Cat) (F: CLeftAdjoint 𝐂 𝐃) (A B: ob 𝐂) (X: Cospan (F A) (F B)) :=
  IsSpan.Build 𝐂 A B (Fspan' X) (up (F:=funcop1 F) (in1 X)) (up (F:=funcop1 F) (in2 X)).

Section s.
Context {𝐂 𝐃: Cat} {F: CLeftAdjoint 𝐂 𝐃} {A B: ob 𝐂}.
Definition Fspan'_hom {X Y: Cospan (F A) (F B)} (f: CospanHom X Y): Fspan' Y ~> Fspan' X := Fhom' (adj F) f.
Lemma is_span_hom_Fspan' (X Y: Cospan (F A) (F B)) (f: CospanHom X Y):
  IsSpanHom 𝐂 A B (Fspan' Y) (Fspan' X) (Fspan'_hom f).
Proof.
  split; split; cbn; rewrite /Fspan'_hom/=.
Admitted.
HB.instance Definition _ X Y f := @is_span_hom_Fspan' X Y f. 

Definition Fspan'_ (X: Cospan (F A) (F B)): Span A B := Fspan' X.
HB.instance Definition _ :=
  IsBarePreContravariantFunctor.Build (Cospan (F A) (F B)) (Span A B) Fspan'_ (fun X Y f => Fspan'_hom f: SpanHom _ _).
HB.instance Definition _ :=
  IsPreContravariantFunctor'.Build (Cospan (F A) (F B)) (Span A B) Fspan'_ (fun _ _ _ _ H => @Fhom'_eqv _ _ (adj F) _ _ _ _ H).
HB.instance Definition _ :=
  IsContravariantFunctor.Build (Cospan (F A) (F B)) (Span A B) Fspan'_ (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _).

HB.instance Definition _ :=
  IsPreAdjointCF'.Build (Span A B) (Cospan (F A) (F B)) (Fspan_ F) Fspan'_ .
HB.instance Definition _ :=
  IsPreAdjointCF'.Build (Cospan (F A) (F B)) (Span A B) Fspan'_ (Fspan_ F).

Lemma _Fspan_cleftAdjoint: IsCLeftAdjoint (Span A B) (Cospan (F A) (F B)) (Fspan_ F).
Proof.
  split. unshelve esplit. 2: unshelve esplit.
  - unshelve esplit. intro X. cbn. exists (unit' (adj (funcop1 F)) X). split; cbn. split; cbn. 
    sorry.
    split; split. exact: (natural (unit' (adj (funcop1 F)))). 
  - unshelve esplit. intro X. cbn. exists (counit' (adj (funcop1 F)) X). split; cbn. split; cbn. 
    sorry.
    split; split. exact: (natural (counit' (adj (funcop1 F)))).
  - cbn; split=>X/=.
    exact: (unit_counit_l_at' (adj (funcop1 F))).
    exact: (unit_counit_r_at' (adj (funcop1 F))).
Qed.
HB.instance Definition _ := _Fspan_cleftAdjoint.
End s.     

Section s.
Context {𝐂 𝐃: Cat} {F: CAdjointEquivalence 𝐂 𝐃} {A B: ob 𝐂}.
Lemma _Fspan_crightAdjoint: IsCRightAdjoint (Span A B) (Cospan (F A) (F B)) (Fspan_ F).
Proof.
  split. unshelve esplit. 2: unshelve esplit.
  - unshelve esplit. intro X. cbn. exists (unit' (funcop1 F) X). split; cbn. split; cbn. 
    sorry.
    split; split. exact: (natural (unit' (funcop1 F))). 
  - unshelve esplit. intro X. cbn. exists (counit' (funcop1 F) X). split; cbn. split; cbn. 
    sorry.
    split; split. exact: (natural (counit' (funcop1 F))).
  - cbn; split=>X/=.
    exact: (unit_counit_l_at' (funcop1 F)).
    exact: (unit_counit_r_at' (funcop1 F)).
Qed.
HB.instance Definition _ := _Fspan_crightAdjoint.
End s.

Definition spanop {𝐂 A B} := @Fspan_ 𝐂 _ obop A B.
(* TODO: dualise *)
Fail Definition cospanop {𝐂 A B} := @Fcospan_ 𝐂 _ obop A B.
HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) := cadjointEquivalence.on (@spanop _ A B).
(* TODO: dualise *)
Fail HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) := cadjointEquivalence.on (@cospanop _ A B).


(** * (co)products *)

Definition is_product {𝐂: PreCat} (A B: ob 𝐂) (X: Span A B) := is_terminal X.
Definition is_coproduct {𝐂: PreCat} (A B: ob 𝐂) (X: Cospan A B) := is_initial X.

Fail Check fun (C: Cat) (A B: ob C) (X: Span A B) => unify (is_product X) (is_coproduct (spanop X)). 

Definition is_product_op (C: Cat) (A B: ob C) (X: Span A B) (P: is_product X): is_coproduct (spanop X)
  := cladj_terminal spanop P .
(* TODO: dualise *)
Fail Definition is_coproduct_op (C: Cat) (A B: ob C) (X: Cospan A B) (P: is_coproduct X): is_product (cospanop X)
  := cradj_initial cospanop P.

  

#[primitive] 
HB.mixin Record IsProduct {𝐂: PreCat} (A B: ob 𝐂) X of span 𝐂 A B X := {
    #[canonical=no] productP: is_product X;
  }.
#[short(type="Product")]
HB.structure Definition product 𝐂 A B := {X of IsProduct 𝐂 A B X &}.

Definition pair {𝐂: PreCat} {A B: ob 𝐂} (X: Product A B) {Y} (f: Y ~> A) (g: Y ~> B): Y ~> X
  := (unique_morph (productP (mk_span f g))). 
Lemma pairE{𝐂: PreCat} {A B: ob 𝐂} {X: Product A B} {Y} (f: Y ~> A) (g: Y ~> B):
  pair X f g \; pi1 ≡ f ∧ pair X f g \; pi2 ≡ g .
Proof. exact: (span_hom (unique_morph (productP (mk_span f g)))). Qed.

#[primitive] 
HB.mixin Record IsCoproduct {𝐂: PreCat} (A B: ob 𝐂) X of cospan 𝐂 A B X := {
    #[canonical=no] coproductP: is_coproduct X;
  }.
#[short(type="Coproduct")]
HB.structure Definition coproduct 𝐂 A B := {X of IsCoproduct 𝐂 A B X &}.

Definition copair {𝐂: PreCat} {A B: ob 𝐂} (X: Coproduct A B) {Y} (f: A ~> Y) (g: B ~> Y): X ~> Y
  := (unique_morph (coproductP (mk_cospan f g))). 
Lemma copairE{𝐂: PreCat} {A B: ob 𝐂} {X: Coproduct A B} {Y} (f: A ~> Y) (g: B ~> Y):
  in1 \; copair X f g ≡ f ∧ in2 \; copair X f g ≡ g .
Proof. exact: (cospan_hom (unique_morph (coproductP (mk_cospan f g)))). Qed.

Lemma _product_coproduct (𝐂: Cat) A B (X: @Product 𝐂 A B): @IsCoproduct (𝐂^op) (obop A) (obop B) (obop X).
Proof. split. apply: is_product_op. exact/productP. Qed.
HB.instance Definition _ 𝐂 A B X := @_product_coproduct 𝐂 A B X. 
Lemma _coproduct_product (𝐂: Cat) A B (X: @Coproduct 𝐂 A B): @IsProduct (𝐂^op) (obop A) (obop B) (obop X).
Proof. split. apply: is_coproduct_op. exact/coproductP. Qed.
HB.instance Definition _ 𝐂 A B X := @_coproduct_product 𝐂 A B X. 

Lemma copairE'{𝐂: Cat} {A B: ob 𝐂} {X: Coproduct A B} {Y} (f: A ~> Y) (g: B ~> Y):
  in1 \; copair X f g ≡ f ∧ in2 \; copair X f g ≡ g .
Proof.
  move: (@pairE (𝐂^op) _ _ (obop (X: ob _)) _ (morphop f) (morphop g))=>/=.
  rewrite /pair/copair/=. cbn. intro H. 
  Fail exact: H.                (* maybe with cospanop finished? *)
Admitted.


(** * pushouts and pullbacks *)


(** * squares *)

(** the category of morphisms and squares *)

Definition morphism (𝐂: Quiver) := { A: ob 𝐂 & {B: ob 𝐂 & A ~> B }}.
Definition src {𝐂} (f: morphism 𝐂): ob 𝐂 := projT1 f. 
Definition tgt {𝐂} (f: morphism 𝐂): ob 𝐂 := projT1 (projT2 f). 
Coercion mor {𝐂} (f: morphism 𝐂): src f ~> tgt f := projT2 (projT2 f).
Definition Mor {𝐂: Quiver} {A B: ob 𝐂} (f: A ~> B): morphism 𝐂 := existT _ A (existT _ B f).

Definition square {𝐂: PreCat} (f g: morphism 𝐂) :=
  { i: src f ~> src g & { j: tgt f ~> tgt g | i \; g ≡ f \; j }}.
Definition square_src {𝐂: PreCat} (f g: morphism 𝐂) (h: square f g) := projT1 h. 
Definition square_tgt {𝐂: PreCat} (f g: morphism 𝐂) (h: square f g) := proj1_sig (projT2 h). 
Definition squareP {𝐂: PreCat} (f g: morphism 𝐂) (h: square f g): square_src h \; g ≡ f \; square_tgt h := proj2_sig (projT2 h).
Definition Square {𝐂: PreCat} {f g: morphism 𝐂} (i: src f ~> src g) (j: tgt f ~> tgt g) (P: i \; g ≡ f \; j): square f g := existT _ i (exist _ j P).

HB.instance Definition _ (𝐂: PreCat) (f g: morphism 𝐂) :=
  Setoid.copy (square f g) (kernel (fun h => (square_src h, square_tgt h))).
HB.instance Definition _ (𝐂: PreCat) := IsQuiver.Build (morphism 𝐂) square.

Definition square_id {𝐂: Cat} (f: morphism 𝐂): f ~> f.
  exists idmap, idmap. abstract cat.
Defined.

Definition square_comp {𝐂: Cat} (f g h: morphism 𝐂) (i: f ~> g) (j: g ~> h): f ~> h.
  exists (square_src i\;square_src j), (square_tgt i\;square_tgt j).
  abstract (do 2 arewrite squareP; cat). 
Defined.

HB.instance Definition _ (𝐂: Cat) := IsPreCat.Build (morphism 𝐂) square_id square_comp.

Lemma _square_cat (𝐂: Cat):  IsCat (morphism 𝐂).
Proof.
  split. 
  split=>/=; exact: comp1o.
  split=>/=; exact: compo1.
  split=>/=; exact: compoA.
  move=>f g h i i' [i1 i2] j j' [j1 j2]; split; exact/comp_eqv.
Qed.
HB.instance Definition _ 𝐂 := _square_cat 𝐂. 


    



(** * cones/cocones *)

Section s.
  Context {𝐃: Quiver} {𝐂: PreCat} (F: PreFunctor 𝐃 𝐂).
  Definition cone := {C & {p: forall d, F d ~> C | forall d d' (f: d ~> d'), Fhom F f \; p d' ≡ p d }}.
  Definition cone_ob (C: cone): ob 𝐂 := projT1 C. 
  Definition cone_mor (C: cone): forall d, F d ~> cone_ob C := proj1_sig (projT2 C). 
  Lemma coneP (C: cone) d d' (f: d ~> d'): Fhom F f \; cone_mor C d' ≡ cone_mor C d.
  Proof. exact: (proj2_sig (projT2 C)). Qed.

  Definition cone_hom (C D: cone) :=
    { h: cone_ob C ~> cone_ob D | forall d, cone_mor C d \; h ≡ cone_mor D d }.
  Coercion cone_hom_ C D: cone_hom C D -> (cone_ob C ~> cone_ob D) := @proj1_sig _ _. 
  Lemma cone_homP C D (h: cone_hom C D) d: cone_mor C d \; h ≡ cone_mor D d.
  Proof. exact: (proj2_sig h). Qed.
  
  HB.instance Definition _ := IsQuiver.Build cone cone_hom.

  Definition is_limit := @is_initial cone.
  Definition limit := Initial cone.
End s.
Section s.
  Context {𝐃: Quiver} {𝐂: Cat} (F: PreFunctor 𝐃 𝐂).

  Program Definition cone_id (C: cone F): C ~> C := exist _ idmap _.
  Next Obligation. move=>/=C d. cat. Qed.
  Program Definition cone_comp (C D E: cone F) (f: C ~> D) (g: D ~> E): C ~> E :=
    exist _ (f \; g) _.
  Next Obligation.
    move=>C D E f g d. arewrite cone_homP. exact/cone_homP.
  Qed.
  HB.instance Definition _ := IsPreCat.Build (cone F) (@cone_id) (@cone_comp).

  (* TODO with a subcategory construction *)
  Lemma _cone_cat: IsCat (cone F).
  Proof.
    split; intros. 
    - exact: comp1o.
    - exact: compo1.
    - exact: compoA.
    - move=>/=f f' ff g g' gg. exact/comp_eqv.
  Qed.  
  HB.instance Definition _ := _cone_cat. 

End s.

Definition EmptyQuiver (T: Type) := T.
HB.instance Definition _ T := IsQuiver.Build (EmptyQuiver T) (fun _ _ => False). 

Definition Cat0 := EmptyQuiver False.
HB.instance Definition _ := quiver.on Cat0. 
HB.instance Definition _ := IsPreCat.Build Cat0 empty_fun (fun a => @empty_fun _ a). 
Program Definition _cat0 := IsCat.Build Cat0 _ _ _ _.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
HB.instance Definition _ := _cat0.

Module Shape.

Definition DiscreteTwo := bool.
HB.instance Definition _ := quiver.copy DiscreteTwo (EmptyQuiver _). 


Section s.
  Context {𝐂: Quiver}.
  Variables A B: ob 𝐂.
  Definition ob_pair (d: DiscreteTwo) := if d then B else A.
  HB.instance Definition _ := IsPreFunctor.Build _ _ ob_pair (fun _ _ => empty_fun).
End s.
Section s.
  Context {𝐂: PreCat}.
  Variables A B: ob 𝐂.
  Definition ob_pair_cone C (f: A ~> C) (g: B ~> C): cone (ob_pair A B).
    exists C. unshelve eexists. case=>/=. exact: g. exact: f.
    by case.
  Defined.
    
  Lemma sumL: forall C (f: A ~> C) (g: B ~> C),
      iffT
        (is_limit (ob_pair_cone f g))
        (forall C' (f': A ~> C') (g': B ~> C'), Σ! h: C ~> C', f \; h ≡ f' /\ g \; h ≡ g').
  Proof.
    split.
    - move=>L C' f' g'. destruct (L (ob_pair_cone f' g')) as [[h H] _ U].
      exists h. exact: (conj (H false) (H true)).
      cbn in *=>h' H'. apply: (U (exist _ h' _))=>//.
      case; apply H'.
    - move=> H [C' [p U]].       (* ok and boring *)
  Abort.
                    
End s. 

Definition ParallelTwo := bool.
Definition paralleltwo_hom (a b: ParallelTwo): StrictSetoid.type :=
  match a,b with
  | false,true => bool
  | _,_ => False
  end.
HB.instance Definition _ := IsQuiver.Build ParallelTwo paralleltwo_hom.   
  

Section s.
  Context {𝐂: Quiver}.
  Variables A B: ob 𝐂.
  Definition parallel_pair (_ _: A ~> B) (d: ParallelTwo) := if d then B else A.
  Variables f g: A ~> B.
  Definition Fparallel_pair (d d': ParallelTwo): (d ~> d') -> parallel_pair f g d ~> parallel_pair f g d' :=
    match d,d' with
    | false,true => fun b => if b then g else f
    | _,_ => empty_fun
    end.
  HB.instance Definition _ d d' := StrictThusExtensional.Build _ _ (@Fparallel_pair d d'). 
  HB.instance Definition _ := IsPreFunctor.Build _ _ (parallel_pair f g) Fparallel_pair.
End s.

Definition Three := option bool.
Definition span_hom (a b: Three): StrictSetoid.type :=
  match a,b with
  | None,Some _ => Datatypes.unit
  | _,_ => False
  end.
Definition Span := Three.
HB.instance Definition _ := IsQuiver.Build Span span_hom.

Section s.
  Context {𝐂: Quiver}.
  Variables A B C: ob 𝐂.
  Definition span (_: B ~> A) (_: B ~> C) (d: Span) :=
    match d with
    | None => B
    | Some d => if d then C else A
    end.
  Variables (f: B ~> A) (g: B ~> C).
  Definition Fspan (d d': Span): (d ~> d') -> span f g d ~> span f g d' :=
    match d,d' with
    | None,Some false => fun _ => f
    | None,Some true => fun _ => g
    | _,_ => empty_fun
    end.
  HB.instance Definition _ d d' := StrictThusExtensional.Build _ _ (@Fspan d d'). 
  HB.instance Definition _ := IsPreFunctor.Build _ _ (span f g) Fspan.
End s.


Definition CoSpan := Span^op.
(* HB.instance Definition _ := quiver.on CoSpan.  *)
(* Check CoSpan: Quiver. *)

End Shape.
