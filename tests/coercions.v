Require Import cat functor morphisms coalgebra.

Local Open Scope cat_scope.

Check fun (C: Cat) (A: ob C) => A: A ~> A.

Check fun (C: Cat) (a b: ob C) (i: Mono a b) => morphop i: Epi _ _.
Check fun (C: Cat) (a b: ob C) (i: Epi a b) => morphop i: Mono _ _.
Check fun (C: Cat) (a b: ob C) (i: SplitMono a b) => morphop i: SplitEpi _ _.
Check fun (C: Cat) (a b: ob C) (i: SplitEpi a b) => morphop i: SplitMono _ _.
Check fun (C: Cat) (a b: ob C) (i: RegMono a b) => morphop i: RegEpi _ _.
Check fun (C: Cat) (a b: ob C) (i: RegMono a b) => morphop i: Epi _ _.
Check fun (C: Cat) (a b: ob C) (i: RegEpi a b) => morphop i: RegMono _ _.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => morphop i: SplitEpi _ _.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => morphop i: SplitMono _ _.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => morphop i: @SplitEpi (C^op) b a.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => morphop i: @SplitMono (C^op) b a.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => morphop i: b≃_(C^op)a.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => morphop i: obop b ≃ obop a.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => morphop i: _ ≃ _.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => inv i: _ ≃ _.
Check fun (C: Cat) (a b: ob C) (i: a≃b) => inv i: SplitMono _ _.

Check fun (C: Cat) (F: Functor C C) (f: F ~> F) => let G: PreFunctor _ _ := F in f: G ~> G.

Check fun (C: Cat) (F: Functor C C) (A: ob C) => F A.
Check fun (C: Cat) (F: Functor C C) (A: ob C) => F A: _ ~> _.


Check fun (C: Quiver) (A: Initial C) => A: ob C.
Check fun (C: PreCat) (A: Initial C) => A: ob C.
Check fun (C: Cat) (A: Initial C) => A: ob C.

Check fun (C: Quiver) (A: Initial C) => obop A: Terminal (C^op).
Check fun (C: PreCat) (A: Initial C) => obop A: Terminal (C^op).
Check fun (C: Cat) (A: Initial C) => obop A: Terminal (C^op).

Check fun (C: Quiver) (F: ob C -> ob C) (A: Coalgebra F) => C^op: Quiver.  
Check fun (C: Quiver) (F: ob C -> ob C) (A: Coalgebra F) => funcop F: C^op -> C^op.  
Check fun (C: Quiver) (F: ob C -> ob C) (A: Coalgebra F) => obop A: C^op.
Check fun (C: Quiver) (F: ob C -> ob C) (A: Coalgebra F) => obop A: Algebra _.  
Check fun (C: Quiver) (F: ob C -> ob C) (A: Algebra F) => obop A: Coalgebra _.  

Fail Check fun (C: Cat) (F: Functor C C) (A: Coalgebra F) => obop A: Algebra _.  
Fail Check fun (C: Cat) (F: Functor C C) (A: Algebra F) => obop A: Coalgebra _.  
Check fun (C: Cat) (F: Functor C C) (A: Coalgebra F) => obop A: ob (Coalgebra F)^op.  
Check fun (C: Cat) (F: Functor C C) (A: Algebra F) => obop A: ob (Algebra F)^op.  
Check fun (C: Cat) (F: Functor C C) (A: Coalgebra F) => obop (A: ob C): Algebra _.  
Check fun (C: Cat) (F: Functor C C) (A: Algebra F) => obop (A: ob C): Coalgebra _.  

Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: A ~> B) => morphop f: _ ~> _.
Fail Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: A ~> B) => morphop f: Coalghom _ _.
Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: Alghom A B) => Alghomop f: Coalghom _ _.
Fail Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: Alghom A B) => morphop f: Coalghom _ _.
Fail Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: Alghom A B) => morphop f: _ ~>_(Coalgebra _) _.
Fail Check fun (C: Cat) (F: Functor C C) (A B: Algebra F) (f: Alghom A B) => (morphop f: Coalghom _ _): _ ~> _.

Section s.
  Context {C: Cat} (F: Functor C C).
  Check fun A: Algebra F => A: ob _. 
  Check fun A: Algebra F => A: ob C. 
  Check fun A: Algebra F => alg A. 
  Check fun A: Algebra F => alg: F A ~> A. 

  Check fun A: Initial (Algebra F) => A: ob _. 
  Check fun A: Initial (Algebra F) => A: ob (Algebra _). 
  Fail Check fun A: Initial (Algebra F) => A: Algebra _. 
  Check fun A: Initial (Algebra F) => (A: ob (Algebra _)): ob C. 
  Check fun A: Initial (Algebra F) => alg (A: ob (Algebra _)). 
  Check fun A: Initial (Algebra F) => alg: F (A: ob (Algebra _)) ~> _.
End s.
