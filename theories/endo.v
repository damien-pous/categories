(** * the monoidal category of endofunctors *)

Require Export monoidal_def.
From Stdlib Require Import ProofIrrelevance. 

Local Open Scope cat_scope.

Section s.
Context {𝐂: Cat}.
Notation Endo := (𝐂 ≈> 𝐂).

(*TMP-UNIV: functor_comp -> ∘ *)
Definition COMP (FG: Endo*Endo): Endo := functor_comp FG.2 FG.1.

HB.instance Definition _ :=
  IsPreFunctor.Build (Endo*Endo)%type Endo COMP
    (fun FG FG' (fg: FG ~> FG') => ntx_comp' fg.2 fg.1).

Program Definition _COMP_functor :=
  IsFunctor.Build _ _ COMP _ _ _.
Next Obligation.
  move=>FG FG' fg fg' [ff gg].
  exact: ntx_comp'_eqv.
Qed.
Next Obligation. move=>FG A/=. cat. Qed.
Next Obligation.
  move=>FG IJ UV fg ij X/=.
  normalise. rewrite -!compoA.
  apply comp_eqv=>//.
  normalise. by rewrite natural. 
Qed.
HB.instance Definition _ := _COMP_functor.

HB.instance Definition _endofunctor_UIP :=
  HasUIP.Build (Functor 𝐂 𝐂) (fun _ _ => proof_irrelevance _). 

HB.instance Definition _ := 
  @HasMonoidalOps.Build (Functor 𝐂 𝐂) functor_id COMP.  
Program Definition _endofunctor_premonoidal :=
  @IsPreMonoidal.Build (Functor 𝐂 𝐂) _ _ _ _ _ _.  
Next Obligation. move=>F G H. by apply: same_functor. Defined.
Next Obligation. move=>F. by apply: same_functor. Defined.
Next Obligation. move=>F. by apply: same_functor. Defined.
Next Obligation. cbn; intros. cat. Qed.
Next Obligation. cbn; intros. cat. Qed.
Next Obligation. cbn; intros. cat. Qed.
HB.instance Definition _ := _endofunctor_premonoidal.

Program Definition _endofunctor_monoidal :=
  @IsMonoidal.Build (Functor 𝐂 𝐂) _ _.
Next Obligation. intros F G H I A. cbn. normalise. cat. Qed.
Next Obligation. intros F G A. cbn. normalise. cat. Qed.
HB.instance Definition _ := _endofunctor_monoidal.

End s.
