(** bicategories *)

Require Export morphisms.

Local Open Scope cat_scope.

(** * bicategories *)
#[primitive] HB.mixin Record HomCats 𝐂 of BAREQUIVER 𝐂  := {
    #[canonical=no] hom_cat: forall a b: ob 𝐂, CAT.axioms_ (hom a b)
}.
#[short(type="CatQuiver")]
HB.structure Definition CATQUIVER := { 𝐂 of HomCats 𝐂 & }.
HB.instance Definition _ (𝐂: CatQuiver) (a b: ob 𝐂) := hom_cat a b. 

HB.factory Record IsCatQuiver 𝐂 := {
    hom: ob 𝐂 -> ob 𝐂 -> Cat
}.
HB.builders Context 𝐂 of IsCatQuiver 𝐂.
  HB.instance Definition _ := IsBareQuiver.Build 𝐂 hom. 
  HB.instance Definition _ := HomCats.Build 𝐂 (fun a b => CAT.class (hom a b)). 
HB.end.

#[primitive] HB.mixin Record IsBiCat 𝐂 of BAREPRECAT 𝐂 & CATQUIVER 𝐂  := {
    (* comp'22 a bifunctor *)
    #[canonical=no] comp'22: forall {a b c: ob 𝐂} {f f': a ~> b} {g g': b ~> c},
      (f ~> f') -> (g ~> g') -> (f \; g) ~> (f' \; g');
    #[canonical=no] comp'22_eqv: forall a b c f f' g g',
      Proper (eqv ==> eqv ==> eqv) (@comp'22 a b c f f' g g');
    #[canonical=no] comp'22_id: forall {a b c: ob 𝐂} (f: a ~> b) (g: b ~> c),
      comp'22 (idmap f) (idmap g) ≡ idmap (f \; g);
    #[canonical=no] comp'22_comp:
      forall {a b c: ob 𝐂} (f f' f'': a ~> b) (g g' g'': b ~> c)
        (i: f ~> f') (i': f' ~> f'') (j: g ~> g') (j': g' ~> g''),
        comp'22 (i \; i') (j \; j') ≡ comp'22 i j \; comp'22 i' j';
    (* unitors and associators *)
    #[canonical=no] comp'1o: forall {a b: ob 𝐂} (f: a ~> b), idmap \; f ≃ f;
    #[canonical=no] comp'o1: forall {a b: ob 𝐂} (f: a ~> b), f \; idmap ≃ f;
    #[canonical=no] comp'oA: forall {a b c d: ob 𝐂} (f: a ~> b) (g: b ~> c) (h: c ~> d), (f \; g) \; h ≃ f \; (g \; h);
    (* naturality of above transformations *)
    #[canonical=no] comp'1o_nat: forall {a b: ob 𝐂} (f f': a ~> b) (i: f ~> f'), comp'1o f \; i ≡ comp'22 idmap i \; comp'1o f';
    #[canonical=no] comp'o1_nat: forall {a b: ob 𝐂} (f f': a ~> b) (i: f ~> f'), comp'o1 f \; i ≡ comp'22 i idmap \; comp'o1 f';
    #[canonical=no] comp'1A_nat:
    forall {a b c d: ob 𝐂}
      (f f': a ~> b) (i: f ~> f')
      (g g': b ~> c) (j: g ~> g')
      (h h': c ~> d) (k: h ~> h'),
      comp'oA f g h \; comp'22 i (comp'22 j k) ≡ comp'22 (comp'22 i j) k \; comp'oA f' g' h';
    (* missing coherence axioms, waiting for notations *)
    (* #[canonical=no] pentagon: forall A B C D: ob 𝐂, *)
    (*   A · assoc B C D ∘ assoc A (B⊗C) D ∘ assoc A B C · D *)
    (*   ≡ assoc A B (C⊗D) ∘ assoc (A⊗B) C D; *)

    (* #[canonical=no] triangle: forall A B: ob 𝐂, *)
    (*   A · unitl B ∘ assoc A unit B *)
    (*   ≡ unitr A · B;     *)
  }.
#[short(type="BiCat")]
HB.structure Definition BICAT := { 𝐂 of IsBiCat 𝐂 & }.

Arguments comp'22 {_ _ _ _ _ _ _ _}.
Infix "·" := comp'22: cat_scope. 

Arguments comp'1o {_ _ _}.
Arguments comp'o1 {_ _ _}.
Arguments comp'oA {_ _ _ _ _}.

Section s.
  Context {𝐂: BiCat}.
  Implicit Types a b c d: ob 𝐂.
  Record adjunction {a b} (f: a~>b) (g: b~>a) := {
      unit: idmap ~> f \; g;
      counit: g \; f ~> idmap;
      unit_counit_l: unit · idmap \; comp'oA _ _ _ \; idmap · counit ≡ comp'1o _ \; (comp'o1 _)⁻¹;
      unit_counit_r: idmap · unit \; (comp'oA _ _ _)⁻¹ \; counit · idmap ≡ comp'o1 _ \; (comp'1o _)⁻¹;
    }.
End s.
