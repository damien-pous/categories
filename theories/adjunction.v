(** * adjunctions *)

Require Export functor.

Local Open Scope cat_scope.

(** ** indexed by the left adjoint *)

(*TMP-UNIV: revert to nice notations *)
#[primitive] HB.mixin Record isLeftAdjoint {𝐂 𝐃: Cat} F of @functor 𝐂 𝐃 F :=
  { #[canonical=no] radj: 𝐃 ≈> 𝐂; 
    #[canonical=no] unit_: functor_id ~> functor_comp F radj;
    #[canonical=no] counit_: functor_comp radj F ~> functor_id;
    #[canonical=no] unit_counit_l_: idmap ⊚ unit_ \; counit_ ⊚ idmap ≡ ntx_id _;
    #[canonical=no] unit_counit_r_: unit_ ⊚ idmap \; idmap ⊚ counit_ ≡ ntx_id _;
  }.
#[short(type="LeftAdjoint")]
HB.structure Definition leftAdjoint {𝐂 𝐃: Cat} := {F of isLeftAdjoint 𝐂 𝐃 F & }.
Arguments radj {_ _ _}, {_ _}.
Infix "⊣" := LeftAdjoint (at level 79): cat_scope.

Section theory.
Context {𝐂 𝐃: Cat} (F: 𝐂 ⊣ 𝐃).

Definition unit: functor_id ~> functor_comp F (radj F) := unit_. 
Definition counit: functor_comp (radj F) F ~> functor_id := counit_.
Definition unit_counit_l: idmap ⊚ unit \; counit ⊚ idmap ≡ ntx_id _ := @unit_counit_l_ _ _ F.
Definition unit_counit_r: unit ⊚ idmap \; idmap ⊚ counit ≡ ntx_id _ := @unit_counit_r_ _ _ F.

Definition up {A B} (f: F A ~> B): A ~> radj F B :=
  unit A \; Fhom (radj F) f.

Definition dn {A B} (f: A ~> radj F B): F A ~> B :=
  Fhom F f \; counit B.

Lemma up_eqv {A B}: Proper (eqv ==> eqv) (@up A B).
Proof. move=>f f' ff. rewrite/up. apply:comp_eqv=>//. exact/Fhom_eqv. Qed.
HB.instance Definition _ A B := isExtensional.Build _ _ _ (@up_eqv A B). 

Lemma dn_eqv {A B}: Proper (eqv ==> eqv) (@dn A B).
Proof. move=>f f' ff. rewrite/dn. apply:comp_eqv=>//. exact/Fhom_eqv. Qed.
HB.instance Definition _ A B := isExtensional.Build _ _ _ (@dn_eqv A B). 

Goal forall A: ob 𝐂, forall f: F A ~> F A, forall g: A ~> A, f \; Fhom F A \; f ≡ f \; f \; Fhom F (g \; g).
Proof. intros. rewrite Fidmap. rewrite Fcomp. Abort.

Goal forall A: ob 𝐂, forall B: ob 𝐃, forall f: F A ~> B, Fhom F (unit A \; Fhom radj f) \; counit B ≡ Fhom F (unit A) \; Fhom F (Fhom radj f) \; counit B.
  (* something is broken... *)
Proof. intros. Fail rewrite Fcomp.  Abort.

Lemma dn_up {A B} (f: F A ~> B): dn (up f) ≡ f.
Proof.
  (* TOFIX: rewrite this proofs once rewriting works again *)
  rewrite /dn/up/=.
  etransitivity. apply: comp_eqv. 
  apply: Fcomp. reflexivity.
  rewrite compoA.
  etransitivity. apply: comp_eqv. reflexivity.
  apply: (natural counit).
  rewrite -compoA.
  rewrite -{2}(comp1o f).
  apply: comp_eqv=>//.   
  move: (unit_counit_l A).
  simpl. rewrite !cats.
  move=>H. rewrite -H. apply: comp_eqv=>//.
  symmetry; etransitivity. apply: comp_eqv. 2: reflexivity. 2: exact/comp1o. exact/Fidmap.
Qed.

Lemma up_inj {A B} (f f': F A ~> B): up f ≡ up f' -> f ≡ f'.
Proof. move=>H. rewrite -(dn_up f) -(dn_up f'). exact/dn_eqv. Qed.

Lemma up_dn {A B} (f: A ~> radj F B): up (dn f) ≡ f.
Proof.
  (* TOFIX: rewrite this proofs once rewriting works again *)
  rewrite /dn/up/=. 
  etransitivity. apply: comp_eqv. reflexivity. 
  apply: Fcomp. 
  rewrite -compoA.
  etransitivity. apply: comp_eqv. 
  symmetry; apply: (natural unit). reflexivity.
  cbn. rewrite /types_id compoA.
  rewrite -{2}(compo1 f).
  apply: comp_eqv=>//.   
  move: (unit_counit_r B).
  cbn. rewrite /types_id/=/types_id !cats.
  move=>H. rewrite -H. cat. 
Qed.

Lemma dn_inj {A B} (f f': A ~> radj F B): dn f ≡ dn f' -> f ≡ f'.
Proof. move=>H. rewrite -(up_dn f) -(up_dn f'). exact/up_eqv. Qed.

(* TODO: declare up/dn as adjoints from the partialorder lib point of view *)

End theory.
