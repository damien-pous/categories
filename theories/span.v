(** * spans *)

Require Export cat.

Local Open Scope cat_scope.

Record Span {𝐂: Quiver} (A B: 𝐂) :=
  span
    {
      span_ob:> 𝐂;
      spanl: span_ob ~> A;
      spanr: span_ob ~> B;
    }.
Arguments span {_ _ _ _}.
Arguments spanl {_ _ _ _}. 
Arguments spanr {_ _ _ _}. 

Definition Span_morphism {𝐂: PreCat} {A B: 𝐂} (X Y: Span A B) :=
  { h: X ~> Y | spanl ∘ h ≡ spanl /\ spanr ∘ h ≡ spanr }.

HB.instance Definition _ (𝐂: Cat) (A B: 𝐂) :=
  IsQuiver.Build (Span A B) Span_morphism. 
Program Definition _span_precat (𝐂: Cat) (A B: 𝐂) :=
  IsPreCat.Build (Span A B)
    (fun X => exist _ idmap _)
    (fun X Y Z h g => exist _ (g ∘ h) _).
Next Obligation. intros; cbn. by rewrite 2!comp1o. Qed.
Next Obligation.
  intros?????? [h [Hl Hr]] [g [Gl Gr]]; cbn. by rewrite 2!compoA Gl Gr.
Qed.
HB.instance Definition _ 𝐂 A B := @_span_precat 𝐂 A B.

Program Definition _span_cat (𝐂: Cat) (A B: 𝐂) :=
  IsCat.Build (Span A B) _ _ _ _.
Next Obligation. intros. apply: comp1o. Qed.
Next Obligation. intros. apply: compo1. Qed.
Next Obligation. intros. apply: compoA. Qed.
Next Obligation. repeat intro. exact: comp_eqv. Qed.
HB.instance Definition _ 𝐂 A B := @_span_cat 𝐂 A B.
