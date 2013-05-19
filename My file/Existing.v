(*programm1*)
Require Import Arith.

Fixpoint add n m := 
  match n with 0 => m | S p => add p (S m) end.

Lemma addnS : forall n m, add n (S m) = S (add n m).
Proof.
 induction n.
 intros m; simpl.
 reflexivity.
 intros m; simpl.
 apply IHn.
Qed.

Lemma addn0 : forall n, add n 0 = n.
Proof.
 induction n;simpl;auto.
 rewrite addnS.
 rewrite IHn;trivial.
Qed.

Lemma add_comm : forall n m, add n m = add m n.
Proof.
Qed.



(*programm2*)

Inductive color:Type :=
 | white | black | yellow | cyan | magenta | red | blue | green.

Definition compl (c : color) :=
 match c with 
 | white => black 
 | black => white
 | yellow => blue
 | cyan => red
 | magenta => green
 | red => cyan
 | blue => yellow
 | green => magenta
 end.

Lemma compl_injective : forall c c', compl c = compl c' -> c = c'.
Proof.
Qed.
