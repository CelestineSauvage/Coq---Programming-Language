Require Import Arith.

(* We first want to prove that our definition of add satisfies commutativity. *)

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

(* Q1. Prove the following two theorems: beware that you will probably need
  addnS. *)
Lemma addn0 : forall n, add n 0 = n.
Proof.
 induction n;simpl;auto.
 rewrite addnS.
 rewrite IHn;trivial.
Qed.

Lemma add_comm : forall n m, add n m = add m n.
Proof.
 induction n;simpl.
 intro;rewrite addn0;auto.
 intros;rewrite addnS.
 rewrite IHn;trivial.
 rewrite addnS.
 trivial.
Qed.


(* Q2. Now state and prove the associativity of this function. *)

Lemma plus_assoc : forall n m p, add n (add m p)= add (add n m) p.
Proof.
 induction n.
 simpl;auto.
 intros.
 simpl.
 repeat rewrite <- addnS.
 rewrite IHn.
 repeat rewrite addnS.
 simpl.
 rewrite addnS.
 trivial.
Qed.

 
(* Q3. Now state and prove a theorem that expresses that this add function
  returns the same result as plain addition (given by function plus) *)

Lemma add_plus : forall n p, add n p = n+p.
Proof.
  induction n; simpl; auto.
  intro; rewrite addnS.
  rewrite IHn;trivial.
Qed.

(* Note that the theorems about commutativity and associativity could be
  consequences of add_plus. *)

(* Programs about lists.  *)
Require Import List ZArith.

(* We re-use the permutation defined in course C2. *)

Fixpoint multiplicity (n:Z)(l:list Z) : nat := 
  match l with 
    nil => 0%nat 
  | a::l' => if Zeq_bool n a then S (multiplicity n l') else multiplicity n l' 
  end. 

Definition is_perm (l l':list Z) := 
  forall n, multiplicity n l = multiplicity n l'.

(* Q4. Show the following theorem: *)

Lemma multiplicity_app : forall x l1 l2, multiplicity x (l1++l2) =
    multiplicity x l1 + multiplicity x l2.
Proof.
 induction l1;simpl;auto.
 case (Zeq_bool x a).
 intros;rewrite IHl1.
 simpl;auto.
 intros;rewrite IHl1.
 simpl;auto.
Qed.


(* Q5. State and prove a theorem that expresses that element counts are
  preserved by reverse. *)
Require Import ArithRing.

Lemma multiplicity_rev : forall x l, multiplicity x (rev l) = multiplicity x l.
Proof.
 induction l;simpl;auto.
 rewrite multiplicity_app.
 simpl.
 case (Zeq_bool x a).
 rewrite IHl;auto with arith.
 ring.
 rewrite IHl;ring.
Qed.

(* --------------------------------------------*)
(* The following questions are more advanced and can be kept for later. *)

(* Q6. Show the following theorem.  You will probably have an occasion
  to use the ring tactic *)

Lemma is_perm_transpose :
  forall x y l1 l2 l3, is_perm (l1++x::l2++y::l3) (l1++y::l2++x::l3).
Proof.
 intros;unfold is_perm;intros.
 replace (l1 ++ x :: l2 ++ y :: l3) with (l1 ++ (x::nil) ++ l2 ++ (y::nil)++l3).
 2:simpl;auto.
 replace (l1 ++ y:: l2 ++ x :: l3) with (l1 ++ (y::nil) ++ l2 ++ (x::nil)++l3).
 2:simpl;auto.
 repeat rewrite multiplicity_app.
 ring.
Qed.

(* Q5 : What does this function do? *)
Fixpoint mask (A : Type)(m : list bool)(s : list A) {struct m} :=
  match m, s with
  | b :: m', x :: s' => if b then x :: mask A m' s' else mask A m' s'
  | _, _ => nil
  end.

Implicit Arguments mask.

(* Q6 Prove that : *)
Lemma mask_cat A m1 (s1 : list A) :
    length m1 = length s1 ->
  forall m2 s2, mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
Proof.
intros Hm1 m2 s2. 
revert s1 Hm1.
induction m1 as [|b1 m1 IHm]; intros [|x1 s1]; trivial. 
  now intros H; inversion H.
  now intros H; inversion H.
intros Hm1; injection Hm1; intros Hm1'; simpl.
now rewrite (IHm _ Hm1'); case b1.
Qed.

