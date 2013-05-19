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
 Admitted. 
 

 Lemma id_PP : (P -> P) -> P -> P.
 Proof.
 Admitted.


 Lemma imp_dist : (P -> Q -> R) -> (P -> Q) -> P -> R.
 Proof.
 Admitted.

 
 Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
 Proof.
 Admitted.

 Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
 Proof.
 Admitted.

 Lemma ignore_Q : (P -> R) -> P -> Q -> R.
 Proof.
 Admitted.

 Lemma delta_imp : (P -> P -> Q) -> P -> Q.
 Proof.
 Admitted.

 Lemma delta_impR : (P -> Q) -> P -> P -> Q.
 Proof.
 Admitted.

 Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
 Proof.
 Admitted.

 Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
 Proof.
 Admitted.

End Minimal_propositional_logic.


(** Same exercise as the previous one, with full intuitionistic propositional
   logic 

   You may use the tactics intro[s], apply, assumption, destruct, 
                           left, right, split and try to use tactic composition *)


Section propositional_logic.

 Variables P Q R S T : Prop.

 Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
 Proof.
 Admitted.

 Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
 Proof.
 Admitted.

 Lemma not_contrad :  ~(P /\ ~P).
 Proof.
 Admitted.

 Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
 Proof.
 Admitted.


 Lemma not_not_exm : ~ ~ (P \/ ~ P).
 Proof.
 Admitted.

 Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
 Proof.
 Admitted.

 Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
 Proof.
 Admitted.

 Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
 Proof.
 Admitted.

 Lemma or_to_imp : P \/ Q -> ~ P -> Q.
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








