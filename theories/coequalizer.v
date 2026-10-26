(** * coequalizers *)

Require Import cat morphisms equalizer.
Require Import arewrite.

Open Scope cat_scope.

#[primitive] HB.mixin Record IsCoequalizer (𝐂: PreCat) (a b: ob 𝐂) (f g: a ~> b) (x: ob 𝐂) :=
  {
    #[canonical=no] coequalizer: b ~> x;
    #[canonical=no] coequalizerP: is_coequalizer f g coequalizer;
  }.
#[short(type=Coequalizer)]
HB.structure Definition COEQUALIZER 𝐂 a b f g := {x of IsCoequalizer 𝐂 a b f g x}.
Arguments coequalizer {_} [_ _ _ _].

Section s.
Context (𝐂: PreCat) (a b: ob 𝐂) (f g: a ~> b).
Definition mk_coequalizer x (e: b ~> x) (H: is_coequalizer f g e) := x.
HB.instance Definition _ x e H := IsCoequalizer.Build 𝐂 a b f g (@mk_coequalizer x e H) H. 
Definition mk_coequalizer_ x e H: Coequalizer f g := @mk_coequalizer x e H.
End s.

Section s.
Context (𝐂: PreCat) (a b: ob 𝐂).
HB.instance Definition _ f g (y: @Equalizer 𝐂 a b f g) :=
  IsCoequalizer.Build (op 𝐂) (obop b) (obop a) (morphop f) (morphop g) (obop (y: ob 𝐂)) equalizerP.
HB.instance Definition _ f g (y: @Equalizer (op 𝐂) (obop a) (obop b) (morphop f) (morphop g)) :=
  IsCoequalizer.Build 𝐂 b a f g (obop' (y: ob 𝐂)) (equalizerP (s:=y)).
HB.instance Definition _ f g (y: @Coequalizer 𝐂 a b f g) :=
  IsEqualizer.Build (op 𝐂) (obop b) (obop a) (morphop f) (morphop g) (obop (y: ob 𝐂)) coequalizerP.
HB.instance Definition _ f g (y: @Coequalizer (op 𝐂) (obop a) (obop b) (morphop f) (morphop g)) :=
  IsEqualizer.Build 𝐂 b a f g (obop' (y: ob 𝐂)) (coequalizerP (s:=y)).
End s.

Section s.
Context (𝐂: PreCat) (a b: ob 𝐂) (f g: a ~> b).

Lemma coequalizerC x e: @is_coequalizer 𝐂 a b x f g e -> is_coequalizer g f e.
Proof.
  move=>P.
  split. symmetry. exact: P.1.
  move=>y e' H. exact: (P.2 y e' (eqv_sym _ _ H)).
Defined.

Definition CoequalizerC (x: Coequalizer f g): Coequalizer g f :=
  mk_coequalizer (coequalizerC (coequalizerP (s:=x))).
End s.

(** ** categories with all coequalizers *)
#[primitive] HB.mixin Record HasCoequalizers 𝐂 of PRECAT 𝐂 := {
    #[canonical=no] Coeqz: forall a b: ob 𝐂, forall f g: a~>b, Coequalizer f g;
  }.
#[short(type="CatCoeqz")]
HB.structure Definition CATCOEQZ := { 𝐂 of CAT 𝐂 & HasCoequalizers 𝐂 }.
Arguments Coeqz {_ _ _}.

HB.instance Definition _ (𝐂: CatEqz) :=
  HasCoequalizers.Build (𝐂^op) (fun _ _ f g => obop (Eqz (morphop f) (morphop g))).
HB.instance Definition _ (𝐂: CatCoeqz) :=
  HasEqualizers.Build (𝐂^op) (fun _ _ f g => obop (Coeqz (morphop f) (morphop g))).

Section s.
Context {𝐂: CatCoeqz} {a b: ob 𝐂} (f g: a ~> b).

Definition coeqz: b ~> Coeqz f g := coequalizer (Coeqz f g). 
Definition coeqzP: is_coequalizer f g coeqz := coequalizerP. 

End s.
