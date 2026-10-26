(** * equalizers *)

Require Import cat morphisms.
Require Import arewrite.

Open Scope cat_scope.

#[primitive] HB.mixin Record IsEqualizer (𝐂: PreCat) (a b: ob 𝐂) (f g: a ~> b) (x: ob 𝐂) :=
  {
    #[canonical=no] equalizer: x ~> a;
    #[canonical=no] equalizerP: is_equalizer f g equalizer;
  }.
#[short(type=Equalizer)]
HB.structure Definition EQUALIZER 𝐂 a b f g := {x of IsEqualizer 𝐂 a b f g x}.
Arguments equalizer {_} [_ _ _ _].

Section s.
Context (𝐂: PreCat) (a b: ob 𝐂) (f g: a ~> b).
Definition mk_equalizer x (e: x ~> a) (H: is_equalizer f g e) := x.
HB.instance Definition _ x e H := IsEqualizer.Build 𝐂 a b f g (@mk_equalizer x e H) H. 
Definition mk_equalizer_ x e H: Equalizer f g := @mk_equalizer x e H.
End s.

Section s.
Context (𝐂: PreCat) (a b: ob 𝐂) (f g: a ~> b).

Lemma equalizerC x e: @is_equalizer 𝐂 a b x f g e -> is_equalizer g f e.
Proof.
  move=>P.
  split. symmetry. exact: P.1.
  move=>y e' H. exact: (P.2 y e' (eqv_sym _ _ H)).
Defined.

Definition EqualizerC (x: Equalizer f g): Equalizer g f :=
  mk_equalizer (equalizerC (equalizerP (s:=x))).
End s.

(** ** categories with all equalizers *)
#[primitive] HB.mixin Record HasEqualizers 𝐂 of PRECAT 𝐂 := {
    #[canonical=no] Eqz: forall a b: ob 𝐂, forall f g: a~>b, Equalizer f g;
  }.
#[short(type="CatEqz")]
HB.structure Definition CATEQZ := { 𝐂 of CAT 𝐂 & HasEqualizers 𝐂 }.
Arguments Eqz {_ _ _}.

Section s.
Context {𝐂: CatEqz} {a b: ob 𝐂} (f g: a ~> b).

Definition eqz: Eqz f g ~> a := equalizer (Eqz f g). 
Definition eqzP: is_equalizer f g eqz := equalizerP. 

End s.
