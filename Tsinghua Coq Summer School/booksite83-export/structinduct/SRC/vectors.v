Require Import Bvector.


Fixpoint vector_nth (A:Set)(n:nat)(p:nat)(v:vector A p){struct v}
                  : option A :=
  match n,v  with
    _   , Vnil => None
  | 0   , Vcons b  _ _ => Some b
  | S n', Vcons _  p' v' => vector_nth A n'  p' v'
  end.

(* examples *)

Implicit Arguments Vcons [A n].
Implicit Arguments Vnil [A].

Definition v0 := Vcons true  (Vcons false  (Vcons false  (Vnil))).

Implicit Arguments vector_nth [A p].

Eval compute in vector_nth 2 v0 .
Eval compute in vector_nth 1 v0.
Eval compute in vector_nth 0 v0.
Eval compute in vector_nth 10 v0 .

Theorem nth_size : forall (A:Set)(p:nat)(v:vector A p)(n:nat), 
  vector_nth n v  = None <-> p <= n.
Proof.
 induction v;simpl; auto. 
 intro n; case n; simpl; split; auto with arith. 
 intro n0;case n0;simpl;split.
 discriminate 1.
 inversion 1.
 case (IHv n1);auto with arith.
 case (IHv n1);auto with arith.
Qed.




 


 
