(** * adjunctions *)

Require Export functor.

Local Open Scope cat_scope.

(** ** indexed by the left adjoint *)

(*TMP-UNIV: revert to nice notations *)
#[primitive] HB.mixin Record isLeftAdjoint {𝐂 𝐃: Cat} (F: 𝐂 ≈> 𝐃) (* F of @functor 𝐂 𝐃 F *) :=
  { #[canonical=no] radj: 𝐃 ≈> 𝐂; 
    #[canonical=no] unit: functor_id ~> functor_comp F radj;
    #[canonical=no] counit: functor_comp radj F ~> functor_id;
    #[canonical=no] counit_unit: idmap ⊚ counit ∘ unit ⊚ idmap ≡ ntx_id _;
    #[canonical=no] unit_counit: idmap ⊚ unit ∘ counit ⊚ idmap ≡ ntx_id _;
  }.
#[short(type="LeftAdjoint")]
HB.structure Definition leftAdjoint {𝐂 𝐃: Cat} := {F of isLeftAdjoint 𝐂 𝐃 F & }.
Arguments radj {_ _}.
Infix "⊣" := LeftAdjoint (at level 79): cat_scope.

Section theory.
Context {𝐂 𝐃: Cat} (F: 𝐂 ⊣ 𝐃).
Definition up {A B} (f: leftAdjoint.sort F A ~> B): A ~> radj F B :=
  Fhom (radj F) f ∘ unit A.
Definition dn {A B} (f: A ~> radj F B): leftAdjoint.sort F A ~> B :=
  counit B ∘ Fhom (leftAdjoint.sort F) f. 
End theory.
