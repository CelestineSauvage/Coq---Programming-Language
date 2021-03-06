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

 Lemma imp_dist : (P -> Q -> R) -> (P -> Q) -> P -> R.
 Proof.
  intros H H0 p.
  apply H.
  assumption.
  apply H0.
  assumption.
 Qed.

  Lemma imp_dist' : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof.
   intros H H0 p;apply H.
   assumption.
   apply H0;assumption.
  Qed.

 Lemma id_P : P -> P.
 Proof.
  intro H.
  assumption.
 Qed.

 Lemma id_P' : P -> P.
 Proof.
  intro H;assumption.
 Qed.

 Lemma id_PP : (P -> P) -> P -> P.
 Proof.
   intros H p;assumption.
Qed.
 
 Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
 Proof.
  intros H H0 p;apply H0.
  apply H;assumption.
 Qed.


 Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
 Proof.
  intros H q p;apply H;assumption.
Qed.


 Lemma ignore_Q : (P -> R) -> P -> Q -> R.
 Proof.
  intros H p _; apply H;assumption.
 Qed.

 Lemma delta_imp : (P -> P -> Q) -> P -> Q.
 Proof.
  intros H p; apply H;assumption.
 Qed.

 Lemma delta_impR : (P -> Q) -> P -> P -> Q.
 Proof.
  intros H p _;apply H;assumption.
 Qed.

 Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
 Proof.
  intros H H0 H1 p;apply H1;[apply H | apply H0];assumption.
 Qed.


 Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
 Proof.
  intro H;apply H.
  intro H0.
  apply H0.
  intro p;apply H;intro H2.
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
  intro H;destruct H as [p [q r]];split.
  split;assumption.
  assumption.
Qed.

 Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
 Proof.
  intros H H0;destruct H as [H1 H2].
  destruct H0 as [p r].
  (*

   intros [H1 H2] [p r].
  *)
  split;[apply H1|apply H2];assumption.
 Qed.
  

 Lemma not_contrad :  ~(P /\ ~P).
 Proof.
  intros [H1 H2];destruct H2;assumption.
 Qed.


 Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
 Proof.
  intros [[p|q] p'].
  destruct p';assumption.
  assumption.
 Qed.

 Lemma not_not_exm : ~ ~ (P \/ ~ P).
 Proof.
  intro H.
  assert (H0: ~P).
  intro p;destruct H;left; assumption.
  destruct H;right;assumption.
 Qed.

 Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
 Proof.
  intros H;split;intro H0;destruct H.
  left;assumption.
  right;assumption.
 Qed.

 Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
 Proof.
   intros [H H0] [H1 | H1].
   destruct H;assumption.
   destruct H0;assumption.
Qed.

 Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
 Proof.
   intros [H | H] [p q];destruct H;assumption.
 Qed.
 
 Lemma or_to_imp : P \/ Q -> ~ P -> Q.
 Proof.
 intros [H1 | H2] nP.
 destruct nP;assumption.
 assumption.
 Qed.

 Lemma imp_to_not_not_or : (P -> Q) -> ~~(~P \/ Q).
 Proof.
 intros H H0.
 assert (~Q).
 intro H1.
 destruct H0.
 right;assumption.
 apply H0.
 left.
 intro H2.
 destruct H1;auto.
Qed.


 Lemma contraposition : (P -> Q) -> (~Q -> ~P).
Proof.
 intros H nQ Hp.
 apply nQ;apply H;assumption.
Qed.


 Lemma contraposition' : (~P -> ~Q) <-> (~~Q -> ~~P).
Proof.
  split.
  intros H nnQ Hp.
  apply nnQ;apply H;assumption.
  intros H nP nQ.
 apply H.
 intros H0.
 destruct H0;assumption.
 assumption.
 Qed.


 Lemma contraposition'' : (~P -> ~Q) <-> ~~(Q -> P).
 Proof.
  split.
 
  intros H H0.
  assert (not P).
 intro H1;apply H0.
 intros;assumption.
 assert (not Q).
 apply H ;assumption.
 apply H0.
 intro H3;destruct H2;auto.
 intros H H0 H1.
 apply H.
 intro H2.
 destruct H0.
 apply H2;assumption.
Qed.
 
 Section S0.
  Hypothesis H0 : P -> R.
  Hypothesis H1 : ~P -> R.

  Lemma weak_exm : ~~R.
  intro H.
  assert (not P).
  intro H2.
 destruct H;apply H0;assumption.
 destruct H.
 apply H1;assumption.
Qed.

End S0.

End propositional_logic.




