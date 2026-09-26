From elpi Require Import elpi coercion.

Module Self.
  Structure A := { car:> Type }.
  Structure B := { car':> Type }.
  Structure X (T: A) := { elt:> T }.
  Parameter Op: Type -> Type.
  Canonical OpA (T: A) := {| car := Op T |}.
  Canonical BA (T: B) := {| car := T |}.
  (* Set Debug "unification". *)
  Check fun T: A => Op T: A. 
  Check fun T: B => Op T: A. 
  Parameter op: forall (T: A) (t: T), Op T. 
  Canonical opX (T: A) (t: X T) := {| elt := op T t |}.
  Parameter id: forall (T: A) (t: T), T. 
  Canonical idX (T: A) (t: X T) := {| elt := id T t |}.
  Check fun (T: A) (t: X T) => id T t: X _. 
  Fail Check fun (T: A) (t: X T) => op T t: X (Op T). 
  Fail Check fun (T: A) (t: X T) => op T t: X _. 
  Check fun (T: A) (t: X T) => (op T t: car _): X _.
  Print Graph. 
  Elpi Accumulate coercion.db lp:{{ 
      coercion _ V T E R :- 
      coq.unify-eq T {{car lp:A}} ok, 
      coq.unify-eq E {{X lp:A}} ok, 
      !,
      coq.unify-eq V {{elt lp:A lp:W}} ok,
      R = {{ @reverse_coercion lp:E lp:T lp:W lp:V }}
      .
      }}.
  Check fun (T: A) (t: X T) => op T t: X _. 
  Check fun (T: A) (t: X T) => op T t: X (Op T). 

  Check fun T: A => Op T: A. 
  Check fun (T: A) (t: X T) => elt _ (opX T t): X (Op T). 
  Check fun (T: A) (t: X T) => (opX T t): X (Op T). 
  Check fun (T: A) (t: X T) => op T t: X _. 
  Check fun (T: A) (t: X T) => elt _ (op T t). 
End Self.


From HB Require Export structures.

HB.mixin Record isA T := {}.
HB.mixin Record isB T := {}.
HB.structure Definition A := {T of isA T}.
HB.structure Definition AB := {T of isA T & isB T}.

HB.mixin Record isX (T: A.type) (t: T) := {}.
HB.structure Definition X T := {t of isX T t}.

Check fun (T: A.type) (t: X.type T) => t: T. 
Fail Check fun (T: AB.type) (t: X.type T) => t: T.
Check fun (T: AB.type) (t: X.type T) => X.sort _ t: T.

Parameter Op: Type -> Type.

HB.instance Definition _ (T: A.type) := isA.Build (Op T). 
HB.instance Definition _ (T: AB.type) := isB.Build (Op T).

Check fun T: A.type => Op T: A.type.
Check fun T: AB.type => Op T: A.type.
Check fun T: AB.type => Op T: AB.type.

Parameter T1: A.type.
Definition o1 (t: T1): T1 := t.   
HB.instance Definition _ (t: T1) := isX.Build T1 (o1 t).
Check fun (t: X.type T1) => o1 t: X.type _.

Parameter id: forall (T: A.type), T -> T.
HB.instance Definition _ (T: A.type) (t: X.type T) := isX.Build T (id T t).
Check fun (T: A.type) (t: X.type T) => id T t: X.type _.

Parameter op: forall (T: A.type), T -> Op T.
HB.instance Definition _ (T: A.type) (t: X.type T) := isX.Build (Op T) (op T t).
Fail Check fun (T: A.type) (t: X.type T) => op T t: X.type (Op T).
Check fun (T: A.type) (t: X.type T) => hb_op__canonical__hb_X T t: X.type (Op T).

(* coq.typecheck {{@U_op__canonical__hb_X lp:TT lp:VV}} _ ok, *)
(* coq.say "TAC!", *)

Elpi Accumulate coercion.db lp:{{ 
      coercion _ V T E R :- 
      coq.unify-eq T {{A.sort lp:A}} ok, 
      coq.unify-eq E {{X.type lp:A}} ok, 
      !,
      coq.unify-eq V {{X.sort lp:A lp:W}} ok,
      R = {{ @reverse_coercion lp:E lp:T lp:W lp:V }}.
}}.
Check fun (T: A.type) (t: X.type T) => op T t: X.type _.
Check fun (T: A.type) (t: X.type T) => op T t: X.type (Op T).
    
HB.instance Definition _ := isA.Build nat. 
HB.instance Definition _ := isX.Build nat O. 
Check op _ O: X.type _.
Check op _ O: X.type (Op nat).
Check op nat O: X.type _.
Check op nat O: X.type (Op nat).

Check id _ O: X.type _.
Check id _ O: X.type nat.
Check id nat O: X.type _.
Check id nat O: X.type nat.

