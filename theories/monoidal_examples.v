(** * example: composing monoids in monoidal categories *)

Require Import monoidal.
Import NiceNotations.

Local Open Scope cat_scope.

Section warmup.

Context {𝐂: MonoidalCat} (A B C: 𝐂).

Goal forall f: A ⊗ A ~> B, forall g: B ~> C, forall h: B ~> C ⊗ C, (f;g) · h ≡ f·h ; g·C·C.
Proof. intros. mcat. Qed.

Goal forall f: A ⊗ A ~> B, forall g: B ~> C, forall h: B ~> C ⊗ C, (f;g) · h ≡' f·h ;; (g·C)·C.
Proof. intros. mcat. Qed.

End warmup.


(** ** composing two monoids *)
Section two.

Context {𝐂: MonoidalCat} (M N: 𝐂).

Check mcl: (M⊗N)⊗(M⊗N) ~> M⊗(N⊗M)⊗N.

Variable m: M⊗M ~> M.
Variable e: unit ~> M.
Hypothesis mA: m·M ; m ≡' M·m ; m.
Hypothesis em: e·M ; m ≡' M.
Hypothesis me: M·e ; m ≡' M.

Variable n: N⊗N ~> N.
Variable f: unit ~> N.
Hypothesis nA: n·N ; n ≡' N·n ; n.
Hypothesis fn: f·N ; n ≡' N.
Hypothesis nf: N·f ; n ≡' N.

Variable x: N⊗M ~> M⊗N.
Hypothesis nx: n·M ; x ≡' N·x ;; x·N ;; M·n.
Hypothesis ex: N·e ; x ≡' e·N.
Hypothesis mx: N·m ; x ≡' x·M ;; M·x ;; m·N.
Hypothesis fx: f·M ; x ≡' M·f.

Let mn := M·x·N ;; m·n .
Let ef := e·f .

Lemma mnA: mn·M·N ;; mn ≡' M·N·mn ;; mn.
Proof.
  unfold mn.

  transitivity (M·x·N·M·N ;; M·M·[n·M ; x]·N ;; [m·M ; m]·n). mcat.
  rewrite nx.
  rewrite mA.

  transitivity (M·N·M·x·N ;; M·[N·m ; x]·N·N ;; m·[N·n ; n]). 2: mcat.
  rewrite mx.
  rewrite -nA.

  mcat.
Qed.

Lemma efmn: ef·M·N ;; mn ≡' M·N.
Proof.
  unfold ef, mn.
  
  transitivity ([f·M ; x]·N ;; [e·M ; m]·n). mcat.
  rewrite fx.
  rewrite em.
  
  transitivity (M·[f·N ; n]). mcat.
  rewrite fn.
  
  mcat.
Qed.

Lemma mnef: M·N·ef ;; mn ≡' M·N.
Proof.
  unfold ef, mn.

  transitivity (M·[N·e ; x] ;; m·[N·f ; n]). mcat.
  rewrite ex.
  rewrite nf.

  transitivity ([M·e ; m]·N). mcat.
  rewrite me.
  
  mcat.
Qed.

End two.
Print Assumptions mnA.




(** ** composing three monoids (only multiplication here) *)
Section three.

Context {𝐂: MonoidalCat} (M N O: 𝐂).

Variable m: M⊗M ~> M.
Hypothesis mA: m·M ; m ≡' M·m ; m.

Variable n: N⊗N ~> N.
Hypothesis nA: n·N ; n ≡' N·n ; n.

Variable o: O⊗O ~> O.
Hypothesis oA: o·O ; o ≡' O·o ; o.

Variable x: N⊗M ~> M⊗N.
Hypothesis nx: n·M ; x ≡' N·x ;; x·N ;; M·n.
Hypothesis mx: N·m ; x ≡' x·M ;; M·x ;; m·N.

Variable y: O⊗N ~> N⊗O.
Hypothesis oy: o·N ; y ≡' O·y ;; y·O ;; N·o.
Hypothesis ny: O·n ; y ≡' y·N ;; N·y ;; n·O.

Variable z: O⊗M ~> M⊗O.
Hypothesis oz: o·M ; z ≡' O·z ;; z·O ;; M·o.
Hypothesis mz: O·m ; z ≡' z·M ;; M·z ;; m·O.

(* note that we need this additional coherence diagram linking the three distributive laws *)
Hypothesis xyz: y·M ;; N·z ;; x·O ≡' O·x ;; z·N ;; M·y.

Let mno := M·N·z·N·O ;; M·x·y·O ;; m·n·o.

Lemma mnoA: mno·M·N·O ;; mno ≡' M·N·O·mno ;; mno.
Proof.
  unfold mno.

  transitivity (M·N·z·N·O·M·N·O ;; M·N·M·y·O·M·N·O ;; M·N·M·N·o·M·N·O ;; M·x·N·z·N·O ;; m·[n·M ; x]·y·O ;; m·n·o). mcat.
  rewrite nx.

  transitivity (M·N·z·N·O·M·N·O ;; M·N·M·y·O·M·N·O ;; M·N·M·N·[o·M ; z]·N·O ;; M·x·x·O·N·O ;; M·M·x·N·O·N·O ;; m·M·n·y·O ;; m·n·o). mcat.
  rewrite oz.

  transitivity (M·N·z·N·O·M·N·O ;; M·N·M·y·z·N·O ;; M·N·M·N·z·O·N·O ;; M·x·x·O·O·N·O ;; M·M·x·N·O·O·N·O ;; m·M·n·[o·N ; y]·O ;; m·n·o). mcat.
  rewrite oy.

  transitivity (M·N·O·M·N·z·N·O ;; M·N·O·M·x·y·O ;; M·N·[O·m ; z]·n·O·O ;; M·x·y·o ;; m·n·o). 2: mcat.
  rewrite mz.

  transitivity (M·N·O·M·N·z·N·O ;; M·N·z·x·y·O ;; M·N·M·z·n·O·O ;; M·[N·m ; x]·y·o ;; m·n·o). 2: mcat.
  rewrite mx.

  transitivity (M·N·O·M·N·z·N·O ;; M·N·z·x·O·N·O ;; M·x·z·N·O·N·O ;; M·M·x·O·N·y·O ;; M·m·N·[O·n ; y]·o ;; m·n·o). 2: mcat.
  rewrite ny.

  transitivity (M·N·z·N·O·M·N·O ;; M·N·M·y·z·N·O ;; M·N·M·N·z·O·N·O ;; M·x·x·O·y·O ;; M·M·x·N·y·O·O ;; M·M·M·n·N·o·O ;; [m·M ; m]·n·o). mcat.
  rewrite mA.

  transitivity (M·N·z·N·O·M·N·O ;; M·N·M·y·z·N·O ;; M·N·M·N·z·O·N·O ;; M·x·x·O·y·O ;; M·M·x·N·y·O·O ;; M·m·N·N·N·o·O ;; m·[n·N ; n]·o). mcat.
  rewrite nA.

  transitivity (M·N·z·N·O·M·N·O ;; M·N·M·y·z·N·O ;; M·N·M·N·z·O·N·O ;; M·x·x·O·y·O ;; M·M·x·N·y·O·O ;; M·m·N·n·O·O·O ;; m·n·[o·O ; o]). mcat.
  rewrite oA.

  transitivity (M·N·z·N·z·N·O ;; M·x·[y·M ;; N·z ;; x·O]·y·O ;; M·M·x·N·y·O·O ;; M·m·N·n·O·o ;; m·n·o). mcat.
  rewrite xyz.

  mcat.
Qed.

End three.

