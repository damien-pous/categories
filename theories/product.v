(** * terminal objects, products, cartesian (monoidal) categories *)

Require Export span functor.

Local Open Scope cat_scope.

(** Terminal objects *)

Definition isTerminal {𝐂: Quiver} (Z: 𝐂) :=
  forall X, Unique_morph (fun _: X~>Z => True).
Structure Terminal (𝐂: Quiver) := {
    terminal:> 𝐂;
    terminalP: isTerminal terminal;
  }.

(** Products *)

Section PROD.
Context {𝐂: Cat} {A B: 𝐂}.
Definition isProduct := @isTerminal (Span A B).
Definition Product := @Terminal (Span A B).
Coercion ob_Product (X: Product): 𝐂 := span_ob (terminal X). 
Context {AB: Product}.
Let AB': 𝐂 := AB.
Definition fst: AB' ~> A := spanl.
Definition snd: AB' ~> B := spanr.
Definition pair {X} (f: X ~> A) (g: X ~> B): X ~> AB'.
  eapply (terminalP AB (span f g)).
Defined.
Lemma fst_pair {X} (f: 𝐂 X A) (g: 𝐂 X B): fst ∘ pair f g ≡ f.
Proof.
  rewrite /pair. 
  destruct (unique_elt (terminalP AB (span f g))) as [? [H _]].
  apply H. 
Qed.  
Lemma snd_pair {X} (f: 𝐂 X A) (g: 𝐂 X B):
  snd ∘ pair f g ≡ g.
Proof.
  rewrite /pair. 
  destruct (unique_elt (terminalP AB (span f g))) as [? [_ H]].
  apply H. 
Qed.  
Lemma pairU {X} (f: 𝐂 X A) (g: 𝐂 X B) (h: 𝐂 X AB'):
  fst ∘ h ≡ f -> snd ∘ h ≡ g -> h ≡ pair f g.
Proof.
  move=>F G. symmetry.
  by unshelve eapply (uniqueness (terminalP AB (span f g)) (exist _ h _)).
Qed.
Lemma pair_ext {X} (h: 𝐂 X AB'): h ≡ pair (fst ∘ h) (snd ∘ h).
Proof. by apply pairU. Qed.
Instance pair_eqv {X}: Proper (eqv ==> eqv ==> eqv) (@pair X).
Proof.
  move=>f f' ff g g' gg.
  apply pairU; rewrite -?ff -?gg.
  apply fst_pair. apply snd_pair.
Qed.
Lemma prod_ext {X} (f g: 𝐂 X AB'): fst ∘ f ≡ fst ∘ g -> snd ∘ f ≡ snd ∘ g -> f ≡ g.
Proof. move=>F G. rewrite (pair_ext g). by apply pairU. Qed.
End PROD.
Arguments isProduct {_}. 
Arguments Product {_}. 

(** Categories with all finite products (i.e., cartesian monoidal) *)

HB.mixin Record IsCartesian 𝐂 of cat 𝐂 := {
    #[canonical=no] top_: Terminal 𝐂;
    #[canonical=no] prod_: forall A B: 𝐂, Product A B;    
  }.
#[short(type="CCat")]
HB.structure Definition ccat := { 𝐂 of IsCartesian 𝐂 & }.
Definition top {𝐂: CCat}: 𝐂 := terminal top_.
Definition prod {𝐂: CCat} (A B: 𝐂): 𝐂 := span_ob (terminal (prod_ A B)).
Infix "×" := prod (at level 30).

Section prod.
  Context {𝐂: CCat}.
  Definition pair' {X Y Z T: 𝐂} (f: 𝐂 X Y) (g: 𝐂 Z T): 𝐂 (X×Z) (Y×T) :=
    pair (f∘fst) (g∘snd).

  Definition PROD (X: 𝐂*𝐂): 𝐂 := X.1 × X.2. 
  Program Definition _PROD_prefunctor :=
    IsPreFunctor.Build _ _ PROD (fun A B => (efun f => pair' f.1 f.2)).
  Next Obligation.
    move=>/=A B f g [fg1 fg2]; apply: pair_eqv; by rewrite ?fg1 ?fg2. 
  Qed.
  HB.instance Definition _ := _PROD_prefunctor.
  Program Definition _PROD_functor := IsFunctor.Build _ _ PROD _ _.
  Next Obligation.
    symmetry. apply: pairU; by rewrite comp1o compo1.
  Qed.
  Next Obligation.
    symmetry; apply: pairU=>/=;
      rewrite !compoA ?(fst_pair,snd_pair); 
      rewrite -!compoA ?(fst_pair,snd_pair)//.
  Qed.
  HB.instance Definition _ := _PROD_functor. 

  Implicit Types X Y Z T: 𝐂.

  Lemma pair'_iso {X Y X' Y'} (i: X ≃ X') (j: Y ≃ Y'): X×Y ≃ X'×Y'.
  Proof.
   apply: (mk_iso (pair' i j) (pair' i⁻¹ j⁻¹));
     abstract by apply: prod_ext; rewrite compoA ?(fst_pair,snd_pair)
                                  -compoA ?(fst_pair,snd_pair)
                                     compoA ?(isoK,isoK') !cats.
  Defined.
    
  Definition prod_sym X Y: X×Y ≃ Y×X.
  Proof.
   apply: (mk_iso (pair snd fst) (pair snd fst)).
   - by apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) comp1o.
   - by apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) comp1o.
  Defined.

  Definition prod_assoc X Y Z: (X×Y)×Z ≃ X×(Y×Z).
  Proof.
    apply: (mk_iso (pair (fst∘fst) (pair (snd∘fst) snd))
              (pair (pair fst (fst∘snd)) (snd∘snd))).
    - apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) comp1o.
      by rewrite -compoA !fst_pair.
      apply prod_ext; rewrite compoA ?(fst_pair,snd_pair)//.
      by rewrite -compoA fst_pair snd_pair.
    - apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) comp1o.
      apply prod_ext; rewrite compoA ?(fst_pair,snd_pair)//.
      by rewrite -compoA snd_pair fst_pair.
      by rewrite -compoA !snd_pair.
  Defined.

  Definition UNIT (X: Cat1): 𝐂 := top. 
  Program Definition _UNIT_prefunctor :=
    IsPreFunctor.Build _ _ UNIT (fun A B => (efun f => unique_elt (terminalP _ _))).
  Next Obligation.
    move=>/=A B f g fg/=. exact: uniqueness. 
  Qed.
  HB.instance Definition _ := _UNIT_prefunctor.
  Program Definition _UNIT_functor := IsFunctor.Build _ _ UNIT _ _.
  Next Obligation. intro. exact: (uniqueness (terminalP _ _)). Qed.
  Next Obligation. intros. exact: (uniqueness (terminalP _ _)). Qed.
  HB.instance Definition _ := _UNIT_functor. 
  
  Definition prod_unitl X: top×X ≃ X.
  Proof.
    apply: (mk_iso snd (pair (unique_elt (terminalP _ X)) idmap)).
    - apply snd_pair.
    - apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) ?compo1 comp1o//.
      exact: (Unicity (terminalP top_ _)).
  Defined.
  
  Definition prod_unitr X: X×top ≃ X.
  Proof.
    apply: (mk_iso fst (pair idmap (unique_elt (terminalP _ X)))).
    - apply fst_pair.
    - apply prod_ext; rewrite compoA ?(fst_pair,snd_pair) ?compo1 comp1o//.
      exact: (Unicity (terminalP top_ _)).
  Defined.
  
End prod.



Definition cat_top: Terminal Cat.
  exists (Cat1: Cat)=>X.
  unshelve eexists=>//.
  exact (functor_cst (tt: Cat1)).
  move=>F _/=. split.
  repeat unshelve eexists. 
Defined.

Definition cat_prod (C D: Cat): Product C D.
  unshelve eexists. exists (C * D: Cat)%type.
  unshelve eexists. exact Datatypes.fst. 
  unshelve eexists. split. unshelve eexists. exact Datatypes.fst. sorry. sorry. 
  unshelve eexists. exact Datatypes.snd. 
  unshelve eexists. split. unshelve eexists. exact Datatypes.snd. sorry. sorry.
  move=>X. cbn.
  unshelve eexists=>//.
  unshelve eexists. cbn.
  unshelve eexists. move=>x. exact: (@spanl _ _ _ X x, @spanr _ _ _ X x).
  unshelve eexists.
  unshelve eexists.
  move=>A B. unshelve eexists.
  move=>f. split=>/=.
  exact: (Fhom (@spanl _ _ _ X) f).
  exact: (Fhom (@spanr _ _ _ X) f).
  sorry.
  sorry.
  cbn. rewrite /functor_comp/=. sorry.
  cbn. sorry.
Defined.
HB.instance Definition _ := IsCartesian.Build Cat cat_top cat_prod.


(** Bifunctors *)

Definition app11 {A B D: Cat} (F: A×B ~> D) (X: A) (Y: B): D := F(X,Y).
Definition app22 {A B D: Cat} (F: A×B ~> D) {X X' Y Y'}
  (f: A X X') (g: B Y Y')
  : D (app11 F X Y) (app11 F X' Y') :=
  @Fhom _ _ F (X,Y) (X',Y') (f,g).
Instance app22_eqv {A B D F X X' Y Y'}: Proper (eqv ==> eqv ==> eqv) (@app22 A B D F X X' Y Y').
Proof. intros ??? ???. by apply extensional. Qed.

Definition times {X X' Y Y': Cat}
  (f: X ~> X')
  (g: Y ~> Y')
  : X×Y ~> X'×Y' :=
  app22 (@PROD Cat: Functor _ _) f g.
Instance times_eqv {X X' Y Y'}: Proper (eqv ==> eqv ==> eqv) (@times X X' Y Y').
Proof. apply (app22_eqv (F:=@PROD Cat: Functor _ _)). Qed.
