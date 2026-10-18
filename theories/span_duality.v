(** explicit duality between spans and cospans *)
(* (TO BE PORTED) *)

Require Export cospan functor.
Require Import arewrite.

Local Open Scope cat_scope.

(** ** duality Span <-> Cospan *)

Definition Fspan {𝐂 𝐃: BareQuiver} (F: ob 𝐂 -> ob 𝐃) {A B: ob 𝐂} (X: Span A B): ob 𝐃 := F X.
HB.instance Definition _ 𝐂 𝐃 (F: BarePreFunctor 𝐂 𝐃) (A B: ob 𝐂) (X: Span A B) :=
  IsSpan.Build 𝐃 (F A) (F B) (Fspan F X) (Fhom F pi1) (Fhom F pi2).
HB.instance Definition _ 𝐂 𝐃 (F: BarePreContravariantFunctor 𝐂 𝐃) (A B: ob 𝐂) (X: Span A B) :=
  IsCospan.Build 𝐃 (F A) (F B) (Fspan F X) (Fhom' F pi1) (Fhom' F pi2).

Definition Fspan_hom {𝐂 𝐃: PreCat} (F: BarePreFunctor 𝐂 𝐃) {A B: ob 𝐂} {X Y: Span A B} (f: Spanhom X Y): Fspan F X ~> Fspan F Y := Fhom F f.
Lemma spanhom_Fspan {𝐂 𝐃: PreCat} {F: Functor 𝐂 𝐃} {A B: ob 𝐂} (X Y: Span A B) (f: Spanhom X Y):
  @spanhom _ (F A) (F B) (Fspan F X) (Fspan F Y) pi1 pi2 pi1 pi2 (Fspan_hom F f).
Proof. split; rewrite /=-Fcomp; apply: Fhom_eqv; apply SpanH. Qed.
HB.instance Definition _ 𝐂 𝐃 F A B X Y f := @is_spanhom_Fspan 𝐂 𝐃 F A B X Y f. 

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

Definition Fcospan_ {𝐂 𝐃} (F: BarePreContravariantFunctor 𝐂 𝐃) {A B: ob 𝐂} (X: Cospan A B): Span (F A) (F B) := Fcospan F X.
HB.instance Definition _ {𝐂 𝐃: PreCat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} :=
  IsBarePreContravariantFunctor.Build (Cospan A B) (Span (F A) (F B)) (Fcospan_ F)
    (fun X Y f => Fcospan_hom' F f: SpanHom _ _).
HB.instance Definition _ {𝐂 𝐃: PreCat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} :=
  IsPreContravariantFunctor'.Build (Cospan A B) (Span (F A) (F B)) (Fcospan_ F) (fun _ _ _ _ H => @Fhom'_eqv _ _ F _ _ _ _ H).
HB.instance Definition _ {𝐂 𝐃: Cat} {F: ContravariantFunctor 𝐂 𝐃} {A B: ob 𝐂} :=
  IsContravariantFunctor.Build (Cospan A B) (Span (F A) (F B)) (Fcospan_ F) (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _).

Definition Fcospan' {𝐂 𝐃} (F: PreAdjointCF 𝐂 𝐃) {A B: ob 𝐂} (X: Span (F A) (F B)): ob 𝐂 := adj F X.
HB.instance Definition _ (𝐂 𝐃: Cat) (F: CRightAdjoint 𝐂 𝐃) (A B: ob 𝐂) (X: Span (F A) (F B)) :=
  IsCospan.Build 𝐂 A B (Fcospan' X) (up (F:=funcop2 F) (pi1 X)) (up (F:=funcop2 F) (pi2 X)).

Section s.
Context {𝐂 𝐃: Cat} {F: CLeftAdjoint 𝐂 𝐃} {A B: ob 𝐂}.
Definition Fspan'_hom {X Y: Cospan (F A) (F B)} (f: CospanHom X Y): Fspan' Y ~> Fspan' X := Fhom' (adj F) f.
Lemma is_span_hom_Fspan' (X Y: Cospan (F A) (F B)) (f: CospanHom X Y):
  IsSpanHom 𝐂 A B (Fspan' Y) (Fspan' X) (Fspan'_hom f).
Proof.
  have [/(Fhom'_eqv (F:=adj F))H1 /(Fhom'_eqv (F:=adj F))H2] := cospan_hom f.
  split; split; rewrite /pi1/pi2/=/up/= -compoA -Fcomp'; exact/comp_eqv.
Qed.
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
  - split=>X/=.
    exact: (unit_counit_l_at' (adj (funcop1 F))).
    exact: (unit_counit_r_at' (adj (funcop1 F))).
Defined.
HB.instance Definition _ := _Fspan_cleftAdjoint.
End s.     

Section s.
Context {𝐂 𝐃: Cat} {F: CAdjointEquivalence 𝐂 𝐃} {A B: ob 𝐂}.
Lemma _Fspan_crightAdjoint: IsCRightAdjoint (Span A B) (Cospan (F A) (F B)) (Fspan_ F).
Proof.
  split. unshelve esplit. 2: unshelve esplit.
  - unshelve esplit. intro X. exists (unit' (funcop1 F) X). split; cbn. split; cbn. 
    sorry.
    split; split. exact: (natural (unit' (funcop1 F))). 
  - unshelve esplit. intro X. exists (counit' (funcop1 F) X). split; cbn. split; cbn. 
    sorry.
    split; split. exact: (natural (counit' (funcop1 F))).
  - split=>X/=.
    exact: (unit_counit_l_at' (funcop1 F)).
    exact: (unit_counit_r_at' (funcop1 F)).
Defined.
HB.instance Definition _ := _Fspan_crightAdjoint.
End s.


Section s.
Context {𝐂 𝐃: Cat} {F: CRightAdjoint 𝐂 𝐃} {A B: ob 𝐂}.
Definition Fcospan'_hom {X Y: Span (F A) (F B)} (f: SpanHom X Y): Fcospan' Y ~> Fcospan' X := Fhom' (adj F) f.
Lemma is_cospan_hom_Fcospan' (X Y: Span (F A) (F B)) (f: SpanHom X Y):
  IsCospanHom 𝐂 A B (Fcospan' Y) (Fcospan' X) (Fcospan'_hom f).
Proof. split. case: (is_span_hom_Fspan' (F:=funcop F) (morphop f)). cbn. exact. Qed.
HB.instance Definition _ X Y f := @is_cospan_hom_Fcospan' X Y f. 

Definition Fcospan'_ (X: Span (F A) (F B)): Cospan A B := Fcospan' X.
HB.instance Definition _ :=
  IsBarePreContravariantFunctor.Build (Span (F A) (F B)) (Cospan A B) Fcospan'_ (fun X Y f => Fcospan'_hom f: CospanHom _ _).
HB.instance Definition _ :=
  IsPreContravariantFunctor'.Build (Span (F A) (F B)) (Cospan A B) Fcospan'_ (fun _ _ _ _ H => @Fhom'_eqv _ _ (adj F) _ _ _ _ H).
HB.instance Definition _ :=
  IsContravariantFunctor.Build (Span (F A) (F B)) (Cospan A B) Fcospan'_ (fun _ => Fidmap') (fun _ _ _ _ _ => Fcomp' _ _).

HB.instance Definition _ :=
  IsPreAdjointCF'.Build (Cospan A B) (Span (F A) (F B)) (Fcospan_ F) Fcospan'_ .
HB.instance Definition _ :=
  IsPreAdjointCF'.Build (Span (F A) (F B)) (Cospan A B) Fcospan'_ (Fcospan_ F).

Lemma _Fcospan_crightAdjoint: IsCRightAdjoint (Cospan A B) (Span (F A) (F B)) (Fcospan_ F).
Proof.
  split.
  case: (@_Fspan_cleftAdjoint _ _ (funcop F) (obop A) (obop B)).
  cbn=>H.
  apply: Adj.op21=>/=.
Admitted.
HB.instance Definition _ := _Fcospan_crightAdjoint.
End s.

Section s.
Context {𝐂 𝐃: Cat} {F: CAdjointEquivalence 𝐂 𝐃} {A B: ob 𝐂}.
Lemma _Fcospan_cleftAdjoint: IsCLeftAdjoint (Cospan A B) (Span (F A) (F B)) (Fcospan_ F).
Proof.
  split.
  case: (@_Fspan_crightAdjoint _ _ (funcop F) (obop A) (obop B)).
  cbn=>H.
  apply: Adj.op12=>/=.
Admitted.
HB.instance Definition _ := _Fcospan_cleftAdjoint.
End s.


Definition spanop {𝐂 A B} := @Fspan_ 𝐂 _ obop A B.
HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) := cadjointEquivalence.on (@spanop _ A B).

Definition cospanop {𝐂 A B} := @Fcospan_ 𝐂 _ obop A B.
HB.instance Definition _ (𝐂: Cat) (A B: ob 𝐂) := cadjointEquivalence.on (@cospanop _ A B).
