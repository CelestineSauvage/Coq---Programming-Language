(* solution proposed by Laurent Théry *)
Require Import Bvector.

Section Empty_Vectors.
 Variable A : Set.


 Definition vector_id : forall n : nat, vector A n -> vector A n.
  intros n; case n.
  intros H'; exact (Vnil A).
  intros n1 H'; exact H'.
 Defined.

 (* Prove that it is indeed the identity *)

 Theorem vector_id_is_id : forall n (v: vector A n), v = vector_id n v.
  intros n v; case v; simpl in |- *; auto.
 Qed.

(* And the trick is done *)

 Theorem vector_eq_0 : forall v : vector A 0, v = Vnil A.
  intros v; exact (vector_id_is_id 0 v).
 Qed.

End Empty_Vectors.
