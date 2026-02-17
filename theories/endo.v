(** * the monoidal category of endofunctors *)

Require Export monoidal_def.
From Stdlib Require Import ProofIrrelevance. 

Local Open Scope cat_scope.

Section s.
Context {𝐂: Cat}.
Notation Endo := (𝐂 ~> 𝐂).

Definition COMP (FG: Endo*Endo): Endo := FG.1 ∘ FG.2.

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
  HasUIP.Build (Functor 𝐂 𝐂) (fun _ _ => proof_irrelevance _) (fun _ _ => proof_irrelevance _). 

Program Definition _endofunctor_premonoidal :=
  @IsPreMonoidal.Build (Functor 𝐂 𝐂) functor_id COMP _ _ _.  
Next Obligation.
  unshelve apply: iso_ntx.
  - move=>[[X Y] Z]/=. apply: same_functor. done. 
  - move=>[[F G] H] [[F' G'] H'] [[f g] h] X. abstract (cbn; cat).
Defined.
Next Obligation.
  unshelve apply: iso_ntx.
  - move=>[[] Z]/=. apply: same_functor. done. 
  - move=>[[] H] [[] H'] [[] h] X. abstract (cbn; cat). 
Defined.
Next Obligation.
  unshelve apply: iso_ntx.
  - move=>[Z []]/=. apply: same_functor. done. 
  - move=>[H []] [H' []] [h []] X. abstract (cbn; cat). 
Defined.
HB.instance Definition _ := _endofunctor_premonoidal.

Program Definition _endofunctor_monoidal :=
  @IsMonoidal.Build (Functor 𝐂 𝐂) _ _.
Next Obligation. intros F G H I A. cbn. normalise. cat. Qed.
Next Obligation. intros F G A. cbn. normalise. cat. Qed.
HB.instance Definition _ := _endofunctor_monoidal.

End s.
