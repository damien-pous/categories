(** * decision procedure for monoidal categories *)

Require Import arity monoidal_def monoidal_maclane monoidal_gmaclane.
From Stdlib Require Import List.

Local Open Scope cat_scope.


(** morphism expressions *)
Section s.
  Context {𝐂: PreMonoidalCat}.
  Implicit Types A B C D: 𝐂.
  Implicit Types a b c d: gtree 𝐂.
  Implicit Types n m p q: arity 𝐂.

  (* "tree-morphisms" (the reified ones) *)
  Inductive tmor: gtree 𝐂 -> gtree 𝐂 -> Type :=
  | t_var: forall a b, (a ~> b) -> tmor a b
  | t_mcl: forall s t, gNf s = gNf t -> tmor s t
  | t_comp: forall a b c, tmor a b -> tmor b c -> tmor a c
  | t_tens: forall a b c d, tmor a b -> tmor c d -> tmor (gt_tensor a c) (gt_tensor b d).

  Fixpoint eval_tmor a b (u: tmor a b): a ~> b :=
    match u with
    | t_var f => f
    | t_mcl E => eval_gmaclane (find_gMacLane E)
    | t_comp f g => eval_tmor f \; eval_tmor g
    | t_tens f g => eval_tmor f · eval_tmor g
    end.
  
  (* strict "arity-morphisms" *)
  Inductive amor: arity 𝐂 -> arity 𝐂 -> Type :=
  | a_var: forall n m, (n ~> m) -> amor n m
  | a_id: forall n, amor n n
  | a_comp: forall n m p, amor n m -> amor m p -> amor n p
  | a_tens: forall n m p q, amor n m -> amor p q -> amor (n++p) (m++q).
  Arguments a_var [_ _]&. 

  Definition a_mcl n m: n = m -> amor n m.
    destruct 1. exact/a_id.
  Defined.

  Fixpoint eval_amor n m (u: amor n m): n ~> m :=
    match u with
    | a_var f => f
    | a_id _ => idmap
    | a_comp f g => eval_amor f \; eval_amor g
    | a_tens f g => acast (eval_amor f · eval_amor g)
    end.

  Fixpoint gNf_mor a b (u: tmor a b): amor (gNf a) (gNf b) :=
    match u in tmor a b return amor (gNf a) (gNf b) with
    | t_var f => a_var (acast f)
    | t_mcl E => a_mcl E
    | t_comp f g => a_comp (gNf_mor f) (gNf_mor g)
    | t_tens f g => 
        a_comp (a_mcl (gNf_tensor _ _))
       (a_comp (a_tens (gNf_mor f) (gNf_mor g))
               (a_mcl (esym (gNf_tensor _ _))))
    end.

End s.
Arguments t_mcl {_ _ _}&_.

Section s.
Context {𝐂: MonoidalCat}.
Implicit Types A B C D: 𝐂.
Implicit Types a b c d: gtree 𝐂.
Implicit Types n m p q: arity 𝐂.

Lemma eval_a_mcl n m (e: n = m):
  eval_amor (a_mcl e) ≡ find_gMacLane (f_equal (fun l => gNf (gt_trees (gt_ar l))) e).
Proof. destruct e=>/=. gMacLane. Qed.

Lemma eval_gNf_mor_tens a b c d (f: tmor a b) (g: tmor c d):
  eval_amor (gNf_mor (t_tens f g)) ≡ acast (eval_amor (gNf_mor f) · eval_amor (gNf_mor g)).
Proof.
  simpl. set u := (_·_). set v := cast u.
  apply: (eqv_trans _ (acast v) _). rewrite 2!eval_a_mcl /cast-lock.
  repeat apply: comp_eqv=>//; gMacLane.
  rewrite castI. gMacLane.
Qed.

Theorem eval_gNf_mor a b (f: tmor a b):
  eval_tmor f ≡ acast (eval_amor (gNf_mor f)). 
Proof.
  induction f.
  - by rewrite /= castIK. 
  - rewrite /=eval_a_mcl/=. gMacLane. 
  - rewrite /= IHf1 IHf2 cast_comp.
    rewrite 2!comp_cast. gMacLane. 
  - rewrite eval_gNf_mor_tens /= {}IHf1 {}IHf2. 
    rewrite tensor_cast castI. gMacLane.
Qed.

End s.

(** * decision tactic for monoidal categories *)

Module M.

(** * reified terms and decision tactic *)
Section s.
Context {𝐂: PreMonoidalCat}.
Implicit Types A B C D: 𝐂.
Implicit Types a b c d: arity 𝐂.

(** normalised terms *)

Inductive row: arity 𝐂 -> arity 𝐂 -> Type :=
| rnil: forall a, row a a
| rcons: forall a [b b'] (u: b ~> b') [c c'], row c c' -> row (a ++ b ++ c) (a ++ b' ++ c').
Arguments rnil {_}, _. 
Inductive nmor a: arity 𝐂 -> Type :=
| nnil: nmor a a
| ncons: forall [b c], nmor a b -> row b c -> nmor a c.
Arguments nnil {_}, _. 

Fixpoint eval_row a b (r: row a b): a ~> b :=
  match r with
  | rnil => idmap
  | rcons a u r => acast ((eval_arity a · u) · eval_row r)
  end.
Coercion eval_row: row >-> Setoid.sort.

Fixpoint eval_nmor a b (r: nmor a b): a ~> b :=
  match r with
  | nnil => idmap
  | ncons u r => r ∘ eval_nmor u
  end.
Coercion eval_nmor: nmor >-> Setoid.sort.



(** casting operations on terms *)

Notation rcast f := (cast2' (T:=row) f find_eq_arity find_eq_arity).
Notation ncast f := (cast2' (T:=nmor) f find_eq_arity find_eq_arity).

(** ** normalisation helpers *)

Definition ncons' [a b c] (u: nmor a b) (r: row b c): nmor a c :=
  match r with
  | rnil => fun u => u
  | r => fun u => ncons u r
  end u.

Definition nvar [a b] (f: a ~> b): nmor a b :=
  ncast (ncons nnil (rcons nil f (rnil nil))).

Definition nmcl [a b] (E: a = b): nmor a b :=
  cast2' nnil erefl E.                                         

Definition rext_left a b c (f: row b c): row (a++b) (a++c) :=
  match f with
  | rnil => rnil
  | rcons a' u f => rcast (rcons (a++a') u f)
  end.
Fixpoint next_left a b c (f: nmor b c): nmor (a++b) (a++c) :=
  match f with
  | nnil => nnil
  | ncons u f => ncons (next_left a u) (rext_left a f)
  end.

Fixpoint rext_right a b c (f: row b c): row (b++a) (c++a) :=
  match f with
  | rnil => rnil
  | rcons a' u f => rcast (rcons a' u (rext_right a f))
  end.
Fixpoint next_right a b c (f: nmor b c): nmor (b++a) (c++a) :=
  match f with
  | nnil => nnil
  | ncons u f => ncons (next_right a u) (rext_right a f)
  end.

Fixpoint rtensor a a' b b' (f: row a a') (g: row b b'): row (a++b) (a'++b') :=
  match f,g with
  | rnil, rnil => rnil
  | rnil a, rcons a' v g => rcast (rcons (a++a') v g)
  | rcons a u f, _ => rcast (rcons a u (rtensor f g))
  end.

Fixpoint ntensor a a' b b' (f: nmor a a') (g: nmor b b'): nmor (a++b) (a'++b') :=
  match f,g with
  | nnil,_ => next_left a g
  | ncons f r,nnil => next_right b (ncons f r)
  | ncons f r,ncons g s => ncons (ntensor f g) (rtensor r s)
  end.

(* relative arities *)
Variant zarity :=
  | zO
  | zP (a: _)
  | zN (a: _).
Implicit Type z: zarity.
Definition opp z :=
  match z with
  | zO => zO
  | zP a => zN a
  | zN a => zP a
  end.

(* b = z·b' when z>=0 *)
Definition sync_r z b b' :=
  match z with
  | zO => b=b'
  | zP z => b=z++b'
  | zN z => b'=z++b
  end.
(* a' = a·z when z>=0 *)
Definition sync_l z a a' :=
  match z with
  | zO => a=a'
  | zP z => a'=a++z
  | zN z => a=a'++z
  end.

Lemma sync_lC X z c d: sync_l z c d -> sync_l z (X::c) (X::d).
Proof.
  by case: z=>/=[ |b|b] /=E; (* unfold acons, aapp; *) f_equal. 
Defined.

Lemma sync_lO z u v: sync_l z u v -> sync_l (opp z) v u.
Proof. by case: z. Defined.

Lemma sync_rO z u v: sync_r z u v -> sync_r (opp z) v u.
Proof. by case: z. Defined.

Fixpoint locate [a a' b b']: a++a' = b++b' -> {z & sync_l z a b * sync_r z a' b' }%type.
  case:a=>[ |X u] in b *.
  - case: b=>[ |b v] E.
    by exists zO.
    by exists (zP (b::v)). 
  - case: b=>[ |b v] E. 
    by exists (zN (X::u)). 
    injection E=>E' <-. 
    case: (locate _ _ _ _ E') => [z [Z Z']].
    exists z. split=>//. by apply: sync_lC. 
Defined.
Fixpoint locate' [a a' b b' z]: sync_l z a b -> sync_r z a' b' -> a++a' = b++b'.
  case:a=>[ |X u] in b *.
  - case: b=>[ |b v]; case: z =>//= ?<-//.
  - case: b=>[ |b v]/=; case: z =>//=.
    -- move=>[ |b q] // [-> ->] -> //.
    -- move=>[-> ->] -> //.
    -- move=>c[-> ->] -> //. by rewrite -aappA.
    -- move=>c[-> ->] -> //. by rewrite -aappA.
Defined.

Definition before [a a' b b']:
  a++a' = b++b' -> option {c | b = a++c /\ a' = c++b' }.
  move=>E. case: (locate E)=>[[ |c|c] /=[D D']].
  apply: Some. exists nil. by rewrite aappU.
  apply: Some. by exists c.
  apply: None. 
Defined.

Variant tworows z a c: Type :=
  | rtwo: forall b b', row a b -> row b' c -> sync_r z b b' -> tworows z a c.

#[local] Hint Extern 0 => exact: find_eq_arity: core.
Fixpoint zrcomp (n: nat) [a b b' c] z (f: row a b) (g: row b' c): sync_r z b b' -> tworows z a c.
  (* default case (out of fuel) *)
  case:n=>[ |n]. esplit. exact: f. exact: g.  assumption. specialize (zrcomp n). clear n.
  (* real case *)
  case: z=>[ |d|d]/=.
  (* d=0 *)
  - case: f=>[{a}i|{a}i n' n u s t f].
    move=>->. esplit. exact: g. exact: rnil. reflexivity. 
    case: g=>[{b'}j|{b'} j m m' v x y g].
    move=><-. esplit. exact: (rcons i u f). exact: rnil. reflexivity.
    move=>E.
    move:(eq_sym (eq_rect _ _ (eq_sym E) _ (eq_sym (aappA _ _ _))))=>E'.
    case: (before E')=>[[in_j /=[J' J]]| ].
    (* i+n<=j *)
    case: (zrcomp _ _ _ _ zO f (rcons in_j v g) J)=>d e f' g' /=Z.
    esplit. exact: (rcons i u f').
    apply: cast2'. exact: (rext_left (i++n) g'). reflexivity. 
    by rewrite J'.
    by rewrite Z.    
    move {E'}. 
    move:{E}(eq_sym (eq_rect _ _ E _ (eq_sym (aappA _ _ _))))=>E.
    case: (before E)=>[[in_i /=[I' I]]| ].
    (* j+m<=i *)
    case: (zrcomp _ _ _ _ zO (rcons in_i u f) g (eq_sym I))=>d e f' g' /=Z.
    esplit.
    apply: cast2'. exact: (rcons j v f'). 2: reflexivity. 
    by rewrite I'. 
    apply: cast2'. exact: (rext_left (j++m') g'). reflexivity. 
    done. 
    by rewrite Z.

    (* otherwise *)
    move:{E}(eq_sym (eq_rect _ _ E _ (eq_sym (aappA _ _ _))))=>E.
    case: (locate E)=>d [D D'].
    case: (zrcomp _ _ _ _ _ f g D')=>e e' f' g' Z. 
    esplit. exact: (rcons i u f'). exact: (rcons j v g'). 
    simpl. rewrite -2!aappA. apply: locate'. apply: D. apply: Z.

  (* d>0 *)
  - case: f=>[{}j|{}j n' n u s' s {}f] E. 
    -- esplit. apply: cast2'. apply: rext_left g. 4: exact: rnil.
       2: by rewrite E. 1,2: reflexivity.
    -- case: (before (eq_sym E))=>[[d_j [D D']]| ].       
       --- case: (zrcomp _ _ _ _ zO (rcons d_j u f) g (eq_sym D'))=>?? f' g' /=Z.
           esplit. apply: cast2'. apply: rext_left. 2: exact: f'. 4: exact g'.
           2: by rewrite D aappA. reflexivity. by simpl; f_equal.
       --- move:{E}(eq_sym (eq_rect _ _ (eq_sym E) _ (eq_sym (aappA _ _ _))))=>E.
           case: (locate E)=>d' [D D'].
           case: (zrcomp _ _ _ _ d' f g D')=>x y f' g' Z.
           esplit. exact: (rcons j u f'). exact: g'.
           rewrite -aappA. apply: locate'. apply: D. apply: Z.

  (* d<0 *)
  - case: g=>[{}i|{}i m m' v t t' {}g] E. 
    -- esplit. exact: f. exact: rnil. assumption. 
    -- case: (before (eq_sym E))=>[[d_i [D D']]| ].       
       --- case: (zrcomp _ _ _ _ zO f (rcons d_i v g) D')=>?? f' g' /=Z.
           esplit. exact f'. apply: cast2'. apply: rext_left g'.
           2: reflexivity. 2: by rewrite D aappA. by simpl; f_equal.
       --- move:{E}(eq_sym (eq_rect _ _ (eq_sym E) _ (eq_sym (aappA _ _ _))))=>E.
           case: (locate (eq_sym E))=>d' [D D'].
           case: (zrcomp _ _ _ _ d' f g D')=>x y f' g' Z.
           esplit. exact f'. exact: (rcons i v g').
           rewrite -aappA. apply: locate'. apply: sync_lO D. apply: sync_rO Z.
Defined.
Arguments zrcomp _ [_ _ _ _] _ _ _ _. 

Definition rcomp a b c (r: row a b) (s: row b c): tworows zO a c :=
  zrcomp 500 zO r s eq_refl. 

Fixpoint nrcomp a b c (f: nmor a b) (r: row b c): nmor a c :=
  match f with
  | nnil => fun r => ncons nnil r
  | ncons f s =>
      fun r =>
        match rcomp s r with
        | rtwo s r E => fun f => ncons' (cast2' (nrcomp f s) eq_refl E) r 
        end f
  end r.

Fixpoint ncomp a b c (f: nmor a b) (g: nmor b c): nmor a c :=
  match g with
  | nnil => fun f => f
  | ncons g r => fun f => nrcomp (ncomp f g) r
  end f.

Definition nbcomp a b b' c (f: nmor a b) (m: b = b')(g: nmor b' c): nmor a c :=
  ncomp f (ncomp (nmcl m) g). 

Definition ncast' a a' b' b (i: a = a') (f: nmor a' b') (j: b' = b): nmor a b :=
  ncomp (nmcl i) (ncomp f (nmcl j)). 

(** final term normalisation functions *)

Fixpoint norm a b (u: amor a b): nmor a b :=
  match u with
  | a_var f => nvar f
  | a_id a => nnil a
  | a_comp f g => ncomp (norm f) (norm g)
  | a_tens f g => ntensor (norm f) (norm g)
  end.

End s.
Arguments rtwo {_} _ {_ _ _ _}.

Notation rcast f := (cast2' (T:=row) f find_eq_arity find_eq_arity). 
Notation ncast f := (cast2' (T:=nmor) f find_eq_arity find_eq_arity). 

Section s.
Context {𝐂: MonoidalCat}.
Implicit Types A B C D: 𝐂.
Implicit Types a b c d: arity 𝐂.

Definition gmcl_eq_ar a b (e: a=b): gmaclane (gt_trees (gt_ar a)) (gt_trees (gt_ar b)).
  apply: gmcl_eq. by rewrite e.
Defined.

Lemma eval_rcast {a' a b b'} (f: row a b) (i: a=a') (j: b=b'):
  eval_row (cast2' f i j) ≡ cast' (iso_gmaclane (gmcl_eq_ar (esym i))) (iso_gmaclane (gmcl_eq_ar j)) f.
Proof. destruct i; destruct j. by rewrite castK. Qed.

Lemma eval_ncast {a' a b b'} (f: nmor a b) (i: a=a') (j: b=b'):
  eval_nmor (cast2' f i j) ≡ cast' (iso_gmaclane (gmcl_eq_ar (esym i))) (iso_gmaclane (gmcl_eq_ar j)) f.
Proof. destruct i; destruct j. by rewrite castK. Qed.

Lemma id_app a b: idmap (a++b) ≡ acast (idmap a·idmap b).
Proof. rewrite tensor_id. gMacLane. Qed.

Lemma id_app' a b: idmap (a++b) ≡ acast (idmap (a⊗b)).
Proof. by rewrite id_app tensor_id. Qed.

Lemma id_cast_eq a b (e: a=b): idmap a ≡ cast' (gmcl_eq_ar e) (gmcl_eq_ar (eq_sym e)) (idmap b).
Proof. gMacLane. Qed.

Lemma eval_nvar a b (f: a ~> b): nvar f ≡ f.
Proof.
  rewrite /nmor/=. 
  rewrite eval_ncast/= cats.
  rewrite tensorUl tensorUr.
  by rewrite !castI castK.
Qed.

Lemma eval_rext_left a b c (f: row b c): rext_left a f ≡ acast (eval_arity a · f).
Proof.
  case: f=>[{}b|{}b x x' u i i' f]/=.
  - gMacLane.
  - rewrite eval_rcast/=.
    rewrite id_app !(castI,tensor_cast_l,tensor_cast_r,tensorA).
    gMacLane.
Qed.

Lemma eval_next_left a b c (f: nmor b c): next_left a f ≡ acast (eval_arity a · f).
Proof.
  elim: f=>[|b' v f IH r]/=.
  - gMacLane.
  - rewrite eval_rext_left {}IH.
    rewrite tensor_comp_r_src. 
    by rewrite comp_cast bcompK.
Qed.

Lemma eval_rext_right a b c (f: row b c): rext_right a f ≡ acast (f · eval_arity a).
Proof.
  elim: f=>[{}b|{}b x x' u i i' f IH]/=.
  - gMacLane. 
  - rewrite eval_rcast/= {}IH.
    rewrite !(castI,tensorA,tensor_cast_l,tensor_cast_r).
    gMacLane.
Qed.

Lemma eval_next_right a b c (f: nmor b c): next_right a f ≡ acast (f · eval_arity a).
Proof.
  elim: f=>[|b' v f IH r]/=.
  - gMacLane. 
  - rewrite eval_rext_right {}IH.
    rewrite tensor_comp_l_src. 
    by rewrite comp_cast bcompK.
Qed.

Lemma eval_rtensor a b c d f g: @rtensor _ a b c d f g ≡ acast (f · g).
Proof.
  elim: f=>[{}a|{}a x x' u i i' f IH]/=.
  - case: g=>[{}c|{}c y y' v j j' g]/=.
    -- gMacLane.
    -- rewrite eval_rcast /=.
       rewrite !id_app !(tensor_cast_r,tensor_cast_l,tensorA,castI). 
       gMacLane.
  - rewrite eval_rcast/= {}IH.
    rewrite !(tensor_cast_r,tensor_cast_l,tensorA,castI). 
    gMacLane.
Qed.

Lemma eval_ntensor a b c d f g: @ntensor _ a b c d f g ≡ acast (f · g).
Proof.
  elim: f=>{b}[|a' u f IH r]/= in c d g *.
  - apply: eval_next_left. 
  - case: g=>[|c' v g s]/=.
    -- rewrite eval_rext_right eval_next_right.
       rewrite tensor_comp_l_src. 
       by rewrite comp_cast bcompK. 
    -- rewrite eval_rtensor {}IH.
       rewrite -exchange. 
       by rewrite comp_cast bcompK. 
Qed.

Lemma eval_ncons' a b c f r: @ncons' _ a b c f r ≡ r ∘ f.
Proof. case: r=>[d/=|//=] in f *. cat. Qed.

Lemma gmcl_locate [a a' b b' z]:
  sync_l z a b -> sync_r z a' b' -> gmaclane
                                    (gt_tensor (gt_trees (gt_ar a)) (gt_trees (gt_ar a')))
                                    (gt_tensor (gt_trees (gt_ar b)) (gt_trees (gt_ar b'))).
Proof.
  move=>I J. apply: find_gMacLane. cbn.
  rewrite 2!app_nil_r. exact/(locate' I J).
Qed.

Definition Cz z a c: Type :=
  match z with
  | zO => a ~> c
  | zP d => a ~> (d⊗c)
  | zN d => (d⊗a) ~> c
  end.
Definition Cz_eqv [z a c]: relation (Cz z a c) :=
  match z with zO | zP _ | zN _ => eqv end.
Infix "~" := Cz_eqv (at level 79).
Instance Cz_equivalence {z a c}: Equivalence (@Cz_eqv z a c).
Proof. case: z=>/=*; apply: Equivalence_eqv. Qed.
Definition eval_tworows [z a c] (f: tworows z a c): Cz z a c.
  case: f=>b b' r s.
  case: z=>[|d|d] /=E.
  - exact: (s ∘ cast' blocked_id (gmcl_eq_ar E) r). 
  - apply: (idmap · s ∘ cast' blocked_id _ r).
    find_gmaclane'. abstract by rewrite /=E -app_assoc.
  - apply: (s ∘ cast' blocked_id _ (idmap · r)).
    find_gmaclane'. abstract by rewrite /=app_assoc E.
Defined.
Coercion eval_tworows: tworows >-> Cz.

Variant tr_spec [a b c d z] (r: row a b) (s: row c d) (bc: sync_r z b c): tworows z a d -> Prop :=
  tr_spec_:
    forall b' c' (r': row a b') (s': row c' d) (bc': sync_r z b' c'),
      rtwo z r s bc ~ rtwo z r' s' bc'
      -> tr_spec r s bc (rtwo z r' s' bc').

Lemma castK' A' A B B' (i: A'≃A) (j: B≃B') f: f ≡ cast' (blocked_inv i) (blocked_inv j) (cast' i j f).
Proof. exact/cast_switch. Qed.

Tactic Notation "recast" hyp(f) constr(A') constr(B') constr(E) :=
  let a' := reify_ob (A': 𝐂) in
  let b' := reify_ob (B': 𝐂) in
  match type of (f: _~> _) with
  | Setoid.sort (?A ~> ?B) =>
      let a := reify_ob A in
      let b := reify_ob B in
      let i := uconstr:(iso_gmaclane (@find_gMacLane _ a' a _)) in
      let j := uconstr:(iso_gmaclane (@find_gMacLane _ b b' _)) in
      let f' := fresh f in
      unshelve erewrite (castK' i j f) ;
      [rewrite //=?(app_assoc,E)//; exact/find_eq_arity
      |rewrite //=?(app_assoc,E)//; exact/find_eq_arity|];
      set f' := (cast f);
      move:f'=>/={}f
  end.

Lemma rcons_rtwo_eqv_l z [a c]
  [b b_] (r: row a b) (s: row b_ c) E
  [b' b'_] (r': row a b') (s': row b'_ c) E'
  h [i i': arity 𝐂] (u: i ~> i') d F F':
  sync_l z (h++i') d -> (* this assumption follows from E and F, but we have it when we use the lemma *)
  rtwo z r s E ~ rtwo z r' s' E' ->
  rtwo (zP d) (rcons h u r) s F ~ rtwo (zP d) (rcons h u r') s' F'.
Proof.
  cbn in F, F'=>S +/=.
  generalize (eval_arity h · u)=>{}u.
  rewrite 2!castI.
  case: z=>[|z|z]/= in S E E' *.
  -- destruct E, E', S.
     rewrite 2!comp_cast_r !bcompK cast_eqv_iff=>H.
     rewrite (id_app h i').
     rewrite 2!tensor_cast_l 2!comp_cast !bcompK.
     apply: cast_eqv.
     rewrite 2!exchange. exact/tensor_eqv.
  -- recast r a (z⊗b_) E.
     recast r' a (z⊗b'_) E'.
     rewrite (id_cast_eq S) !id_app.
     rewrite 2!castI 2!comp_cast_r 2!bcompK cast_eqv_iff=>H.
     rewrite !(tensor_cast_l, tensor_cast_r, castI).
     rewrite (tensor_lr u r) (tensor_lr u r').
     rewrite -tensor_id. set hi := idmap h · idmap i'.
     rewrite 2!comp_cast. apply: cast_eqv.
     rewrite 2!tensorA 2!bcomp_cast_l. apply: cast_eqv.
     rewrite 2!bcompK 2!compoA.
     by rewrite 2!(exchange _ _ _ (idmap z · _)) H.
  -- recast s (z⊗b) c E.
     recast s' (z⊗b') c E'.
     recast u (h⊗i) (d⊗z) S.
     rewrite 2!comp_cast 2!bcompK cast_eqv_iff=>H.
     rewrite !(castI, tensor_cast_l, tensor_cast_r).
     rewrite 2!comp_cast. apply: cast_eqv.
     rewrite (tensor_lr u r) (tensor_lr u r').
     rewrite -tensor_id.
     rewrite 2!tensorA 2!comp_cast_l 2!bcomp_cast_r. apply: cast_eqv.
     rewrite 2!bcompA. rewrite 2!bcompK.
     by rewrite 2!(exchange _ (idmap d)) H.
Qed.

Lemma rcons_rtwo_eqv_r z [a c]
  [b b_] (r: row a b) (s: row b_ c) E
  [b' b'_] (r': row a b') (s': row b'_ c) E'
  h [i i': arity _] (u: i ~> i') d F F': 
  sync_l z d (h++i) -> (* this assumption follows from E and F, but we have it when we use the lemma *)
  rtwo z r s E ~ rtwo z r' s' E' ->
  rtwo (zN d) r (rcons h u s) F ~ rtwo (zN d) r' (rcons h u s') F'.
Proof.
  (* note: dual to [rcons_rtwo_eqv_l] *)
  cbn in F, F'. move=>S +/=.
  generalize (eval_arity h · u)=>{}u.
  case: z=>[|z|z]/= in S E E' *.
  Import SEEOBJ.
  -- destruct E, E'.
     rewrite (id_cast_eq S).
     rewrite 2!comp_cast_r !bcompK cast_eqv_iff=>H.
     rewrite (id_app h i).
     rewrite !(castI,tensor_cast_l,comp_cast). apply: cast_eqv.
     rewrite 2!bcomp_cast_r. apply: cast_eqv.
     rewrite 2!bcompK.
     by rewrite 2!(exchange (_·_)) H.
  -- recast r a (z⊗b_) E.
     recast r' a (z⊗b'_) E'.
     recast u (d⊗z) (h⊗i') S.
     rewrite 2!castI 2!comp_cast_r 2!bcompK cast_eqv_iff=>H.
     rewrite !(castI, tensor_cast_l, tensor_cast_r).
     rewrite 2!comp_cast. apply: cast_eqv.
     rewrite (tensor_rl u s) (tensor_rl u s').
     rewrite -tensor_id.
     rewrite 2!tensorA 2!comp_cast_r 2!bcomp_cast_l. apply: cast_eqv.
     rewrite -2!bcompA. rewrite 2!bcompK.
     by rewrite 2!(exchange _ (idmap d)) H.
  -- recast s (z⊗b) c E.
     recast s' (z⊗b') c E'.
     rewrite (id_cast_eq S) !id_app.
     rewrite 2!comp_cast 2!bcompK cast_eqv_iff=>H.
     rewrite !(tensor_cast_l, tensor_cast_r, castI).
     rewrite (tensor_rl u s) (tensor_rl u s').
     rewrite -tensor_id. set hi := idmap h · idmap i.
     rewrite 2!comp_cast. apply: cast_eqv.
     rewrite 2!tensorA 2!bcomp_cast_r. apply: cast_eqv.
     rewrite 2!bcompK -2!compoA.
     by rewrite 2!(exchange hi) H.
Qed.

Lemma rcons_rtwo_eqv_r0 z [a c]
  [b b_] (r: row a b) (s: row b_ c) E
  [b' b'_] (r': row a b') (s': row b'_ c) E'
  h [i i': arity _] (u: i ~> i') F F': 
  sync_l z nil (h++i) -> (* this assumption follows from E and F, but we have it when we use the lemma *)
  rtwo z r s E ~ rtwo z r' s' E' ->
  rtwo zO r (rcons h u s) F ~ rtwo zO r' (rcons h u s') F'. 
Proof.
  move=>S /rcons_rtwo_eqv_r EE.
  move: (EE h _ _ u nil (eq_sym F) (eq_sym F') S)=>{EE}/=.
  rewrite 2!tensorUl 2!castI.
  rewrite !comp_cast 2!cast_eqv_iff.
  match goal with
  | |- bcomp _ _ ?m ≡ bcomp _ _ ?n -> bcomp _ _ ?m' ≡ bcomp _ _ ?n' =>
      have [-> ->]: m ≡ m' /\ n ≡ n' =>//; split
  end; 
  (* TO IMPROVE *)
  match goal with
  | |- ?f ≡ ?g => change (iso.sort f ≡ iso.sort g)
  end; simpl; gMacLane.  
Qed.

Lemma rcons_rtwo_eqv z [a c]
  [b b_] (r: row a b) (s: row b_ c) E
  [b' b'_] (r': row a b') (s': row b'_ c) E'
  h [i i': arity _] (u: i ~> i')
  k [j j': arity _] (v: j ~> j') F F': 
  sync_l z (h++i') (k++j) -> (* this assumption follows from E and F, but we have it when we use the lemma *)
  rtwo z r s E ~ rtwo z r' s' E' ->
  rtwo zO (rcons h u r) (rcons k v s) F ~ rtwo zO (rcons h u r') (rcons k v s') F'. 
Proof.
  move=>S EE.
  eapply rcons_rtwo_eqv_r0.
  2: eapply rcons_rtwo_eqv_l.
  by cbn. exact S. 
  eapply EE.
  Unshelve. 
  rewrite F/=. exact: find_eq_arity. 
  rewrite F'/=. exact: find_eq_arity. 
Qed.

Lemma zrcomp_spec n a b b' c z bb r s: tr_spec r s bb (@zrcomp _ n a b b' c z r s bb).
Proof.
  elim: n=>[|n IH] in a b b' c z bb r s *. constructor; reflexivity. 
  move: bb. case: z=>[|d|d].
  - case: r=>[{}a bb | {}a x x' u i i' r].
    { destruct bb. constructor=>/=. rewrite 2!castK. cat. }
    case: s=>[{}b bb|{}b y y' v j j' s].
    { destruct bb. by constructor. }
    { move=> bb. simpl. 
      case: before=>[[d [D D']]|].
      { have [b'' c' r' s' bc' /=E] := IH.
        destruct bc'. constructor=>/=.
        rewrite eval_rcast eval_rext_left.
        move: E.
        recast r i (d⊗y⊗j) D'.
        recast s' b'' (d⊗y'⊗j') tt.
        rewrite 2!castI 2!comp_cast tensorA bcomp_cast_l 2!bcompK castI cast_eqv_iff=>E.
        rewrite (id_cast_eq D).
        rewrite (id_app _ d) id_app'.
        generalize (eval_arity a·u)=>au.        
        set ax' := a⊗x' in au *. 
        set ax_ := a⊗x in au *. 
        rewrite !(castI,tensorA). clear -E. 
        rewrite !(tensor_cast_l, tensor_cast_r, tensorA, castI).
        rewrite 2!comp_cast. 
        subst ax_ ax'. 
        unshelve rewrite bexchange. find_gmaclane. find_gmaclane. 2: gMacLane.
        unshelve rewrite bexchange. find_gmaclane. find_gmaclane. 2: gMacLane.
        rewrite !bcompK. apply: cast_eqv.
        rewrite E. cat.
      }
      case: before=>[[d [D D']]|].
      { have [b'' c' r' s' bc' /=E] := IH.
        destruct bc'. constructor=>/=.
        rewrite 2!eval_rcast eval_rext_left /=.
        move: E. clear. 
        rewrite (id_cast_eq D).
        rewrite (id_app _ d) 2!id_app'.
        generalize (eval_arity b·v)=>bv.        
        set by' := b⊗y' in bv *. 
        set by_ := b⊗y in bv *.
        rewrite !(castI,tensorA).
        recast s (d⊗x'⊗i') j' D'.
        recast r' (d⊗x⊗i) b'' tt. clear.
        rewrite castI comp_cast comp_cast_r cast_eqv_iff 2!bcompK=>E.
        rewrite 2!comp_cast !(tensor_cast_l, tensor_cast_r, tensorA).
        rewrite !(castI,bcomp_cast,castI,bcomp_cast_r).
        subst by_ by'. 
        unshelve rewrite bexchange. find_gmaclane. find_gmaclane. 2: gMacLane.
        unshelve rewrite bexchange. find_gmaclane. find_gmaclane. 2: gMacLane.
        rewrite !bcompK. apply: cast_eqv.
        rewrite E. cat. 
      }
      case: locate => z [axby ij].
      have [b'' c' r' s' bc' E] := IH.
      constructor=>/=. move:E. exact: rcons_rtwo_eqv.
    }
    
  - case: r=>[{}a|{}a x x' u i i' r]/=bb/=.
    { constructor=>/=. rewrite eval_rcast eval_rext_left.
      rewrite (id_cast_eq bb) id_app.
      rewrite !castI 2!comp_cast_r. apply: cast_eqv.
      rewrite 2!bcompK. rewrite 2!exchange. cat.
    }
    case: before=>[[e [D D']]|].
    -- have [b'' c' r' s' bc' /=E] := IH.
       constructor=>/=. rewrite eval_rcast eval_rext_left.
       move:E.
       recast r' (e⊗x⊗i) c' bc'.
       recast s (e⊗x'⊗i') c D'.
       rewrite (id_cast_eq D) id_app.
       rewrite !(castI,tensorA,tensor_cast_l,tensor_cast_r).
       rewrite !(comp_cast,comp_cast_r) 2!cast_eqv_iff 4!bcompK=>E.  
       by rewrite !exchange E.
    -- case: locate => z [axd ib].
       have [b'' c' r' s' bc' E] := IH.
       constructor. move: E. exact: rcons_rtwo_eqv_l.  (* z'=zP d *)

  - case: s=>[{}c|{}c y y' v j j' s]/=bb/=.
    by constructor=>/=.
    case: before=>[[e [D D']]|].
    -- have [b'' c' r' s' bc' /=E] := IH.
       constructor=>/=. rewrite eval_rcast eval_rext_left.
       move:E. clear.
       recast r a (e⊗y⊗j) D'.
       recast r' a c' bc'.
       recast s' c' (e⊗y'⊗j') tt.
       rewrite (id_cast_eq D) id_app.
       rewrite !(castI,tensorA,tensor_cast_l,tensor_cast_r).
       rewrite !comp_cast 2!cast_eqv_iff 4!bcompK=>E.
       rewrite !exchange E. cat. 
    -- case: locate => z [axd ib].
       have [b'' c' r' s' bc' E] := IH.
       constructor. move: E. exact: rcons_rtwo_eqv_r. (* z'=zN d *)
Qed.

Lemma eval_nrcomp a b c f r: @nrcomp _ a b c f r ≡ r ∘ f.
Proof.
  elim: f=>[//|a' u f IH s]/= in c r *.
  rewrite /rcomp.
  have [b' c' r' s' bc] := zrcomp_spec.
  destruct bc. 
  rewrite eval_ncons'/= {}IH.
  rewrite 2!castK !compoA. by move=>->.
Qed.

Lemma eval_ncomp a b c f g: @ncomp _ a b c f g ≡ g ∘ f.
Proof.
  elim: g=>[|b' u g IH r]/=.
  - by rewrite compo1.
  - by rewrite eval_nrcomp IH compoA. 
Qed.

Theorem eval_norm a b (u: amor a b): norm u ≡ eval_amor u.
Proof.
  elim: u=>[{}a {}b f|{}a|{}a {}b c f IHf g IHg|{}a {}b c d f IHf g IHg].
  - exact/eval_nvar. 
  - done. 
  - by rewrite eval_ncomp IHf IHg. 
  - by rewrite eval_ntensor IHf IHg.
Qed.

Theorem normalise a b (u v: amor a b):
  norm u ≡ norm v -> eval_amor u ≡ eval_amor v.
Proof. by rewrite 2!eval_norm. Qed.

Corollary normalise_tmor (a b: gtree 𝐂) (u v: tmor a b):
  norm (gNf_mor u) ≡ norm (gNf_mor v) -> eval_tmor u ≡ eval_tmor v.
Proof.
  intro. rewrite 2!eval_gNf_mor.
  apply: cast_eqv=>//. exact/normalise.
Qed.

End s.


(** reification tools *)

Structure reified_mor {𝐂: PreMonoidalCat} (a b: gtree 𝐂) := reify_mor {
  rm:> a ~> b;
  #[canonical=no] rt:> tmor a b;
  #[canonical=no] rtE: rm ≡ eval_tmor rt;
}.
Arguments reify_mor {_}.


Structure reified_mcl {𝐂: PreMonoidalCat} (a b: gtree 𝐂) := reify_mcl {
  rm':> a ≃ b;
  #[canonical=no] rt': gmaclane a b;
  #[canonical=no] rt'E: iso.sort rm' ≡ eval_gmaclane rt';
}.
Arguments reify_mcl {_}.


Section s.
Context {𝐂: MonoidalCat}.
Implicit Types A B C D: 𝐂.
Implicit Types a b c d: gtree 𝐂.

Corollary normalise_rmor (a b: gtree 𝐂) (u v: reified_mor a b):
  norm (gNf_mor u) = norm (gNf_mor v) -> u ≡ v.
Proof.
  intro E. rewrite 2!rtE. apply: normalise_tmor. by rewrite E. 
Qed.

Notation MacLane := (MacLane_cs _ _ (conj erefl erefl)).

Canonical r_var a b (f: a ~> b) :=
  reify_mor a b f (t_var f) eqv_refl.

Canonical r_id a :=
  reify_mor a a idmap (t_mcl erefl) MacLane.

Canonical r_comp a b c (f: reified_mor a b) (g: reified_mor b c) :=
  reify_mor a c (f\;g) (t_comp f g) (comp_eqv _ _ (rtE f) _ _ (rtE g)).

Canonical r_tens a b c d (f: reified_mor a b) (g: reified_mor c d) :=
  reify_mor (gt_tensor a c) (gt_tensor b d) (f·g) (t_tens f g) (tensor_eqv (rtE f) (rtE g)).

Canonical r_gmaclane a b (f: gmaclane a b) e :=
  reify_mor a b (eval_gmaclane f) (t_mcl e) MacLane.

Canonical r_assoc a b c :=
  reify_mor (gt_tensor (gt_tensor a b) c) (gt_tensor a (gt_tensor b c))
    (assoc a b c) (t_mcl erefl) MacLane.

Canonical r_assoc' a b c :=
  reify_mor (gt_tensor a (gt_tensor b c)) (gt_tensor (gt_tensor a b) c)
    (assoc' a b c) (t_mcl erefl) MacLane.

Canonical r_unitl a :=
  reify_mor (gt_tensor gt_unit a) a
    (unitl a) (t_mcl erefl) MacLane.

Canonical r_unitl' a :=
  reify_mor a (gt_tensor gt_unit a)
    (unitl' a) (t_mcl erefl) MacLane.

Canonical r_unitr a :=
  reify_mor (gt_tensor a gt_unit) a
    (unitr a) (t_mcl erefl) MacLane.

Canonical r_unitr' a :=
  reify_mor a (gt_tensor a gt_unit)
    (unitr' a) (t_mcl erefl) MacLane.

Program Canonical r_mcl a b (f: reified_mcl a b) e :=
  reify_mor a b (mcl f) (t_mcl e) _.
Next Obligation. intros. rewrite /mcl rt'E. gMacLane. Qed.

Program Canonical r_bcomp a b b' c (f: reified_mor a b) (g: reified_mor b' c) (m: reified_mcl b b') e :=
  reify_mor a c (bcomp f g m) (t_comp f (t_comp (t_mcl e) g)) _.
Next Obligation. intros. rewrite 2!rtE /bcomp-lock rt'E. gMacLane. Qed.

Program Canonical r_cast a b b' c (f: reified_mcl a b) (g: reified_mcl b' c) (m: reified_mor b b') ef eg :=
  reify_mor a c (cast' f g m) (t_comp (t_mcl ef) (t_comp m (t_mcl eg))) _.
Next Obligation. intros. rewrite rtE /cast-lock 2!rt'E. gMacLane. Qed.

Program Canonical r_maclane a b (f: maclane a b)
  e (A: src_tree f = gtree_tree a) (B: tgt_tree f = gtree_tree b) :=
  reify_mor a b (Maclane.sort f) (t_mcl e) MacLane.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Definition r'_id a :=
  reify_mcl a a idmap (gmcl_id a) (eqv_sym _ _ (eval_gmaclane_id _)).

Program Definition r'_comp a b c (f: reified_mcl a b) (g: reified_mcl b c) :=
  reify_mcl a c (f\;g) (gmcl_comp (rt' f) (rt' g)) _.
Next Obligation. intros. by rewrite /=eval_gmaclane_comp 2!rt'E. Qed.

Program Canonical r'_inv a b (f: reified_mcl a b) :=
  reify_mcl b a (inv f) (gmcl_inv (rt' f)) _.
Next Obligation. intros. rewrite eval_gmaclane_inv. apply: inv_eqv. apply: rt'E. Qed.
                 
Program Definition r'_tens a b c d (f: reified_mcl a b) (g: reified_mcl c d) :=
  reify_mcl (gt_tensor a c) (gt_tensor b d) (f·g) (gmcl_tensor (rt' f) (rt' g)) _.
Next Obligation. intros. by rewrite /=eval_gmaclane_tensor 2!rt'E. Qed.

Definition r'_gmaclane a b (f: gmaclane a b) :=
  reify_mcl a b (iso_gmaclane f) f eqv_refl.

Definition r'_assoc a b c :=
  reify_mcl (gt_tensor (gt_tensor a b) c) (gt_tensor a (gt_tensor b c))
    (assoc_ (eval_gtree a) (eval_gtree b) (eval_gtree c)) (gmcl_assoc _ _ _)
    (eqv_sym _ _ (eval_gmaclane_assoc _ _ _)).

Definition r'_unitl a :=
  reify_mcl (gt_tensor gt_unit a) a
    (unitl_ (eval_gtree a)) (gmcl_unitl _)
    (eqv_sym _ _ (eval_gmaclane_unitl _)).

Definition r'_unitr a :=
  reify_mcl (gt_tensor a gt_unit) a
    (unitr_ (eval_gtree a)) (gmcl_unitr _)
    (eqv_sym _ _ (eval_gmaclane_unitr _)).

(* Program Definition r'_bcomp a b b' c (f: reified_mcl a b) (g: reified_mcl b' c) (m: reified_mcl b b') e := *)
(*   reify_mcl a c (bcomp f g m) (gmcl_comp (rt' f) (gmcl_comp (rt' m) (rt' g))) _. *)
(* Next Obligation. intros. rewrite 2!rtE rt'E /bcomp-lock. gMacLane. Qed. *)

(* Program Definition r_cast a b b' c (f: reified_mcl a b) (g: reified_mcl b' c) (m: reified_mor b b') ef eg := *)
(*   reify_mor a c (cast' f g m) (t_comp (t_mcl ef) (t_comp m (t_mcl eg))) _. *)
(* Next Obligation. intros. rewrite 2!rt'E rtE/cast-lock. gMacLane. Qed. *)


End s.

Ltac reify_iso_mcl f :=
  lazymatch f with
  | @blocked_id _ ?A =>
      let a := reify_ob A in
      constr:(r'_id a)
  | blocked_comp ?f ?g =>
      let u := reify_iso_mcl f in
      let v := reify_iso_mcl g in
      constr:(r'_comp u v)
  | blocked_inv ?f =>
      let m := reify_iso_mcl f in
      constr:(r'_inv m)
  | blocked_tens ?f ?g =>
      let u := reify_iso_mcl f in
      let v := reify_iso_mcl g in
      constr:(r'_tens u v)
  | @blocked_assoc _ ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(r'_assoc a b c)
  | @blocked_assoc' _ ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(r'_inv (r'_assoc a b c))
  | @blocked_unitl _ ?A =>
      let a := reify_ob A in
      constr:(r'_unitl a)
  | @blocked_unitl' _ ?A =>
      let a := reify_ob A in
      constr:(r'_inv (r'_unitl a))
  | @blocked_unitr _ ?A =>
      let a := reify_ob A in
      constr:(r'_unitr a)
  | @blocked_unitr' _ ?A =>
      let a := reify_ob A in
      constr:(r'_inv (r_unitr a))
  | iso.sort ?f =>
      reify_hom_mcl f
  | iso_gmaclane ?m => 
      constr:(r'_gmaclane m)
  | mcl ?f =>
      reify_iso_mcl f 
  | reverse_coercion ?f _ =>
      reify_iso_mcl f
  | _ => fail "could not reify" f "as a MacLane isomorphism"
  end
with reify_hom_mcl f :=
  lazymatch f with
  | idmap ?A =>
      let a := reify_ob A in
      constr:(r'_id a)
  | ?f \; ?g =>
      let u := reify_hom_mcl f in
      let v := reify_hom_mcl g in
      constr:(r'_comp u v)
  | inv ?f =>
      let m := reify_iso_mcl f in
      constr:(r'_inv m)
  | ?f · ?g =>
      let u := reify_hom_mcl f in
      let v := reify_hom_mcl g in
      constr:(r'_tens u v)
  (* | bcomp ?f ?g ?m => *)
  (*     let u := reify_hom_mcl f in *)
  (*     let v := reify_hom_mcl g in *)
  (*     let w := reify_iso_mcl m in *)
  (*     constr:(r_bcomp u v w) *)
  (* | cast' ?f ?g ?m => *)
  (*     let u := reify_iso_mcl f in *)
  (*     let v := reify_iso_mcl g in *)
  (*     let w := reify_hom_mcl m in *)
  (*     constr:(r_cast u v w) *)
  | assoc ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(r'_assoc a b c)
  | assoc' ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(r'_inv (r'_assoc a b c))
  | unitl ?A =>
      let a := reify_ob A in
      constr:(r'_unitl a)
  | unitl' ?A =>
      let a := reify_ob A in
      constr:(r'_inv (r'_unitl a))
  | unitr ?A =>
      let a := reify_ob A in
      constr:(r'_unitr a)
  | unitr' ?A =>
      let a := reify_ob A in
      constr:(r'_inv (r_unitr a))
  | eval_gmaclane ?m => (* (find_gMacLane ?E) *)
      constr:(r'_gmaclane m)
  | reverse_coercion ?f _ => reify_hom_mcl f
  | ?m => fail "could not reify" m "as a MacLane morphism"
  end.

Ltac reify_mor f :=
  lazymatch f with
  | idmap ?A =>
      let a := reify_ob A in
      constr:(r_id a)
  | ?f \; ?g =>
      let u := reify_mor f in
      let v := reify_mor g in
      constr:(r_comp u v)
  | inv ?f =>
      let m := reify_iso_mcl f in
      constr:(r_mcl (r'_inv m) erefl)
  | ?f · ?g =>
      let u := reify_mor f in
      let v := reify_mor g in
      constr:(r_tens u v)
  | bcomp ?f ?g ?m =>
      let u := reify_mor f in
      let v := reify_mor g in
      let w := reify_iso_mcl m in
      constr:(r_bcomp u v w erefl)
  | cast' ?f ?g ?m =>
      let u := reify_iso_mcl f in
      let v := reify_iso_mcl g in
      let w := reify_mor m in
      constr:(r_cast u v w erefl erefl)
  | assoc ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(r_assoc a b c)
  | assoc' ?A ?B ?C =>
      let a := reify_ob A in
      let b := reify_ob B in
      let c := reify_ob C in
      constr:(r_assoc' a b c)
  | unitl ?A =>
      let a := reify_ob A in
      constr:(r_unitl a)
  | unitl' ?A =>
      let a := reify_ob A in
      constr:(r_unitl' a)
  | unitr ?A =>
      let a := reify_ob A in
      constr:(r_unitr a)
  | unitr' ?A =>
      let a := reify_ob A in
      constr:(r_unitr' a)
  | reverse_coercion ?f _ => reify_mor f
  | @eval_gmaclane _ ?s ?t ?m => (* (find_gMacLane ?E) *)
      constr:(@r_gmaclane _ s t m erefl)
  | iso.sort ?f =>
      let m := reify_iso_mcl f in
      constr:(r_mcl m erefl)
  | ?f =>
      lazymatch type of f with
      | Setoid.sort (?A ~> ?B) =>
          let a := reify_ob A in
          let b := reify_ob B in
          constr:(@r_var _ a b f)
      end
  end.


Ltac mcat :=
  lazymatch goal with
    |- ?f ≡ ?g =>
      let u := reify_mor f in
      let v := reify_mor g in
      exact:(@normalise_rmor _ _ _ u v erefl)
  end.

Ltac mcat' :=
  lazymatch goal with
    |- ?f ≡ ?g =>
      let u := reify_mor f in
      idtac "f" u;
      let v := reify_mor g in
      idtac "g" v;
      move:(@normalise_rmor _ _ _ u v)=>//=
  end.

Section tests.
Context {𝐂: MonoidalCat}.
Variables A B C D: 𝐂.
Variables Γ Δ Θ: arity 𝐂.

Goal A ≡ idmap.
Proof. mcat. Qed.
Goal forall (f: A ~> A), idmap∘(f∘f) ≡ (f∘idmap)∘f.
Proof. intros. mcat. Qed.
Goal forall (f g: A ~> A), f ≡ g.
Proof. intros. Fail mcat. Abort. (* should indeed fail *)
Goal forall (f g: A ~> A), f∘(g∘f) ≡ (f∘g)∘f.
Proof. intros. mcat. Qed.
Goal forall (f g: A ~> B), f·g ≡ idmap·g ∘ f·idmap.
Proof. intros. mcat. Qed.
Goal A · unit · B ≡ idmap.
Proof. mcat. Qed.
Goal A · unit · B ≡ mcl.
Proof. mcat. Qed.
Goal (mcl: A⊗unit ~> A) ≡ (acast idmap: A⊗unit ~> A).
Proof. intros. mcat. Qed.
Goal (mcl: A⊗unit ~> A) ∘ (acast idmap: unit⊗A ~> A⊗unit) ∘ (mcl: A ~> unit⊗A) ≡ idmap.
Proof. intros. mcat. Qed.
Goal forall (f: A ~> A) (g: A⊗unit ~> A), g ∘∘ idmap ∘∘ f ≡ g ∘∘ f.
Proof. intros. mcat. Qed.
Goal assoc A B C ≡ mcl.
Proof. mcat. Qed.
Goal assoc A B C ≡ mcl⁻¹.
Proof. mcat. Qed.
Goal assoc A B C ≡ (assoc' A B C)⁻¹.
Proof. Fail mcat. Abort.          (* TOFIX (real CS reification?)*)

Goal (mcl: Γ++Δ ~> Γ⊗Δ) ≡ acast (mcl: Γ++Δ ~> Γ⊗unit⊗Δ).
Proof. mcat. Qed.

Goal forall (f: Γ ~> A) (g: Δ ~> B) (h: A⊗(unit⊗B) ~> C), h ∘∘ f · g ≡ h ∘∘ ((f · idmap) ∘ (idmap · g)).
Proof. intros. Fail mcat. Abort. (* TOFIX (more abstract reification) *)

(* Variable g: (A~>A) -eqv-> (A~>A). *)

(* Goal g (idmap∘idmap) ≡ g mcl. *)
(* Proof. intros. mcat. Qed. *)

(* Goal g (idmap∘idmap) · B ≡ acast (g mcl · mcl)∘idmap. *)
(* Proof. intros. mcat. Qed. *)

(* Variable h: (A~>A) -> (A~>A). *)
(* Hypothesis Hh: Proper (eqv ==> eqv) h.  *)
(* Let r_h := Eval hnf in M.rf_sym1 _ Hh. *)
(* Canonical r_h. *)

(* Goal h (idmap∘idmap) · B ≡ acast (h mcl · mcl)∘idmap. *)
(* Proof. intros. mcat. Qed. *)

(* Goal h (idmap∘g idmap) · B ≡ acast (h (g mcl) · mcl)∘idmap. *)
(* Proof. intros. mcat. Qed. *)

End tests.

End M.
