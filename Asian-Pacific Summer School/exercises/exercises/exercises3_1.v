(** This file contains some lemmas you will have to prove, i.e. replacing
   the "Admitted" joker with a sequence of tactic calls, terminated with a 
   "Qed" command.

   Each lemma should be proved several times :
   first using only elementary tactics :
   intro[s], apply, assumption
   split, left, right, destruct.
   exists, rewrite
   assert (only if you don't find another solution)


   Then, use tactic composition, auto, tauto, firstorder.


Notice that, if you want to keep all solutions, you may use various 
identifiers like in the given example : imp_dist, imp_dist' share
the same statement, with different interactive proofs.


*)




Section Minimal_propositional_logic.
 Variables P Q R S : Prop.

 Lemma id_P : P -> P.
 Proof.
 intros H.
 assumption.
 Qed.
 

 Lemma id_PP : (P -> P) -> P -> P.
 Proof.
 intros h h1.
 assumption.
 Qed.


 Lemma imp_dist : (P -> Q -> R) -> (P -> Q) -> P -> R.
 Proof.
 intros h h1 p.
 apply h.
 assumption.
 apply h1.
 assumption.
 Qed.

 
 Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
 Proof.
 intros h h1 p.
 apply h1.
apply h.
assumption.
 Qed.

 Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
 Proof.
 intros h q p.
 apply h;assumption.
 Qed.

 Lemma ignore_Q : (P -> R) -> P -> Q -> R.
 Proof.
 intros h p q.
 apply h;assumption.
 Qed.

 Lemma delta_imp : (P -> P -> Q) -> P -> Q.
 Proof.
 intros h p.
 apply h;assumption.
 Qed.

 Lemma delta_impR : (P -> Q) -> P -> P -> Q.
 Proof.
 intros h p;apply h;assumption.
 Qed.

 Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
 Proof.
 intros h h1 h2 p.
 apply h2;[apply h|apply h1];assumption.
 Qed.

 Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
 Proof.
 intros h.
 apply h.
intros h1;apply h1.
intros h2.
apply h.
intros h3.
assumption.
 Qed.

End Minimal_propositional_logic.


(** Same exercise as the previous one, with full intuitionistic propositional
   logic 

   You may use the tactics intro[s], apply, assumption, destruct, 
                           left, right, split and try to use tactic composition *)


Section propositional_logic.

 Variables P Q R S T : Prop.

 Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
 Proof.
 intros h.
 destruct h as [p [q r]];split.
split;assumption.
assumption.
 Qed.


 Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
 Proof.
 intros h h1.
 destruct h as [h2 h3].
 destruct h1 as [p r].
 split;[apply h2|apply h3];assumption.
 Qed.

 Lemma not_contrad :  ~(P /\ ~P).
 Proof.
 intros [h1 h2].
 destruct h2.
assumption.
 Qed.

 Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
 Proof.
 intros h1.
 destruct h1 as [[p |q] h2].
 destruct h2.
assumption.
assumption.
 Admitted.


 Lemma not_not_exm : ~ ~ (P \/ ~ P).
 Proof.
 intros H.
  assert (H0: ~P).
  intro p;destruct H;left; assumption.
  destruct H;right;assumption.
 Qed.

 Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
 Proof.
 intros h.
 split;intros h1;destruct h.
 left;assumption.
 right;assumption.
 Qed.

 Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
 Proof.
 intros [h h0].
 intros [p|q].
 destruct h;assumption.
 destruct h0;assumption.
 Qed.

 Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
 Proof.
 intros [h1 | h2] [p q].
 destruct h1;assumption.
 destruct h2;assumption.
 Admitted.

 Lemma or_to_imp : P \/ Q -> ~ P -> Q.
 Proof. 
 Admitted.


 Lemma imp_to_not_not_or : (P -> Q) -> ~~(~P \/ Q).
 Admitted.

 Lemma contraposition : (P -> Q) -> (~Q -> ~P).
 Admitted.

 Lemma contraposition' : (~P -> ~Q) <-> (~~Q -> ~~P).
 Admitted.

 Lemma contraposition'' : (~P -> ~Q) <-> ~~(Q -> P).
 Admitted.
 
 Section S0.
  Hypothesis H0 : P -> R.
  Hypothesis H1 : ~P -> R.

  Lemma weak_exm : ~~R.
  Admitted.

End S0.

Check weak_exm.



 
 (* Now, you may invent and solve your own exercises ! 
    Note that you can trust the tactic tauto: if it fails, then your formula
    is probably not (intuitionnistically) provable *)
(*
Lemma contraposition''' : (~P -> ~Q) <-> (Q -> P).
Proof.
 tauto.
Toplevel input, characters 8-13:
Error: tauto failed.
*)
End propositional_logic.

(* Now observe that the section mechanism discharges also the local
variables P, Q, R, etc. *)

Check and_imp_dist.








