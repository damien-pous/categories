(** * the Cartesian category of categories *)

(* we isolate this part of the library for now:
   its needs universe polymorphism, which is not supported by HB, yet
   as a workaround, we temporarily deactivate universe-checking
 *)
Require Export span functor product.

Local Open Scope cat_scope.

Unset Universe Checking.

HB.instance Definition _ := IsQuiver.Build Cat Functor.
HB.instance Definition _ := IsPreCat.Build Cat (@functor_id) (@functor_comp).

Program Definition _cat_cat := IsCat.Build Cat _ _ _ _.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. split. exact: same_functor. Qed.
Next Obligation. intros. exact: functor_comp_eqv. Qed.
HB.instance Definition _ := _cat_cat.

Definition cat_top: Terminal Cat.
  exists (Cat1: Cat)=>X.
  unshelve eexists=>//.
  exact (functor_cst (tt: Cat1)).
  move=>F _/=. split.
  repeat unshelve eexists. 
Defined.

Definition cat_prod (C D: Cat): Product C D.
  unshelve eexists.
  exists (C * D: Cat)%type.
  exact: (Datatypes.fst: Functor _ _). 
  exact: (Datatypes.snd: Functor _ _).
  unshelve eexists=>//. 
  exists ((types_pair' (spanl (s:=X)) (spanr (s:=X))): Functor _ _).
  split; split; exact: same_functor.
  destruct X as [X L R]=>/=[[F [[HL] [HR]]]] _. cbn. split.
  apply: iso_trans. apply: types_pair'_iso; apply: iso_sym; eassumption.
  clear. unshelve apply: mk_iso.
  { unshelve eexists.
    - split; exact: idmap; split; split; split=>/=; cat.
    - repeat split=>/=; cat. }
  { unshelve eexists.
    - split; exact: idmap; split; split; split=>/=; cat.
    - repeat split=>/=; cat. }
  split=>/=; cat. 
  split=>/=; cat. 
Defined.
HB.instance Definition _ := IsCartesian.Build Cat cat_top cat_prod.

Unset Universe Checking.

Definition times {X X' Y Y': Cat}
  (f: X ~> X') (g: Y ~> Y'): X×Y ~> X'×Y' :=
  app22 (@PROD Cat: Functor _ _) f g.
Instance times_eqv {X X' Y Y'}: Proper (eqv ==> eqv ==> eqv) (@times X X' Y Y').
Proof. apply (app22_eqv (F:=@PROD Cat: Functor _ _)). Qed.

(** a nicer definition for premonoidal categories *)

#[primitive] HB.factory Record IsPreMonoidal' 𝐂 of cat 𝐂 := {
    #[canonical=no] unit: 𝐂;
    #[canonical=no] tensor: (𝐂*𝐂)%type ≈> 𝐂;
    
    (* w.r.t nlab: https://ncatlab.org/nlab/show/monoidal+category *)
    (*    assoc = α, unitl = λ, unitr = ρ *)
    #[canonical=no] assoc_:
    tensor ∘ times tensor idmap
      ≈
    tensor ∘ times idmap tensor ∘ (prod_assoc _ _ _)¹;
    #[canonical=no] unitl_:
    tensor ∘ (times (functor_cst unit) idmap)
      ≈
    (@prod_unitl Cat _)¹;
    #[canonical=no] unitr_: 
    tensor ∘ (times idmap (functor_cst unit))
      ≈
    (@prod_unitr Cat _)¹;
  }.

(*
Lemma ntx_assoc [A B A' B' A'' B''] (f: A ~> B) (g: A' ~> B') (h: A'' ~> B''):
  assoc _ _ _ ∘ (f · g) · h ≡ f · (g · h) ∘ assoc _ _ _.
Proof. exact: (@natural _ _ _ _ (assoc_¹) (_,_,_) (_,_,_) (f,g,h)). Qed.

Lemma ntx_assoc' [A B A' B' A'' B''] (f: A ~> B) (g: A' ~> B') (h: A'' ~> B''):
  assoc' _ _ _ ∘ f · (g · h) ≡ (f · g) · h ∘ assoc' _ _ _.
Proof. exact: (@natural _ _ _ _ (assoc_⁻¹) (_,_,_) (_,_,_) (f,g,h)). Qed.

Lemma ntx_unitl [A B] (f: A ~> B): unitl _ ∘ unit · f ≡ f ∘ unitl _.
Proof. exact: (@natural _ _ _ _ (unitl_¹) (tt,A) (tt,B) (idmap,f)). Qed.

Lemma ntx_unitl' [A B] (f: A ~> B): unitl' _ ∘ f ≡ unit · f ∘ unitl' _.
Proof. exact: (@natural _ _ _ _ (unitl_⁻¹) (tt,A) (tt,B) (idmap,f)). Qed.

Lemma ntx_unitr [A B] (f: A ~> B): unitr _ ∘ f · unit ≡ f ∘ unitr _.
Proof. exact: (@natural _ _ _ _ (unitr_¹) (A,tt) (B,tt) (f,idmap)). Qed.

Lemma ntx_unitr' [A B] (f: A ~> B): unitr' _ ∘ f ≡ f · unit ∘ unitr' _.
Proof. exact: (@natural _ _ _ _ (unitr_⁻¹) (A,tt) (B,tt) (f,idmap)). Qed.
*)
