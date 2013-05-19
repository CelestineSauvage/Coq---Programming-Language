Require Export Arith.

Definition my_le (n p:nat) :=
  forall P : nat -> Prop,
   P n ->
   (forall q : nat, P q -> P (S q)) ->
   P p.

Theorem my_le_n : forall n:nat, my_le n n.
Proof.
 intros n P Hn HS ; assumption.
Qed.

Theorem my_le_S : forall n p:nat,
                  my_le n p -> my_le n (S p).
Proof.
 intros n p H P Hn HS.
 apply HS; apply H; assumption.
Qed.


Theorem my_le_le : forall n p:nat,
                    my_le n p -> n <= p.
Proof.
 intros n p H; apply H; auto with arith.
Qed.
