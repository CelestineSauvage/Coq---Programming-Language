(** Syntax and semantics of the language called IMP, a small
    imperative structured language (see lecture 7) *)

Require Import Coq.Program.Equality. 
Require Import Bool.             
Require Import ZArith.           
Require Import Sequences.    (* Please compile this file first ! *)    

Open Scope Z_scope.             

(** * 1. Abstract syntax *)

(** Variables are identified by integers. *)
Definition ident : Type := Z.

Definition eq_ident: forall (x y: ident), {x=y}+{x<>y} := Z_eq_dec.

(** Syntax of arithmetic expressions  *)
Inductive aexp : Type :=
  | Const: Z -> aexp                    (**r constant *)
  | Var: ident -> aexp                  (**r variable *)
  | Plus: aexp -> aexp -> aexp          (**r sum [a1 + a2] *)
  | Minus: aexp -> aexp -> aexp.         (**r difference [a1 - a2] *)

(** Syntax of boolean expressions.  
    Boolean expressions are used as conditions in [if] and [while] commands. *)
Inductive bexp : Type :=
  | TRUE: bexp                          (**r always true *)
  | FALSE: bexp                         (**r always false *)
  | Eq: aexp -> aexp -> bexp            (**r equality test [a1 == a2] *)
  | Le: aexp -> aexp -> bexp            (**r less or equal test [a1 <= a2] *)
  | Not: bexp -> bexp                   (**r negation [!b] *)
  | And: bexp -> bexp -> bexp.          (**r conjunction [b1 & b2] *)

(** Syntax of commands ("statements"). *)
Inductive command : Type :=
  | Skip                                (**r do nothing *)
  | Assign: ident -> aexp -> command    (**r assignment [x = a;] *)
  | Seq: command -> command -> command  (**r sequence [c1; c2] *)
  | If: bexp -> command -> command -> command (**r conditional [if (b) { c1 } else {c2}] *)
  | While: bexp -> command -> command.  (**r loop [while (b) { c }] *)

Definition vx : ident := 1.
Definition vy : ident := 2.
Definition vq : ident := 3.
Definition vr : ident := 4.

(* Define the following commands : 
- assignment "vr = vx"
- the infinite loop such that its condition is always true and its body is the skip command 
- the euclidian division, corresponding to the following algorithm
<<
                      r = x;
                      q = 0;
                      while (y <= r) {
                          r = r - y;
                          q = q + 1;
                      }
>>
*)

Definition assign1 : command :=  (* TO DO ! *)

Definition infinite_loop : command := (* TO DO ! *)

Definition euclidean_division : command := (* TO DO ! *)

(** * 2. Denotational semantics: evaluation of expressions *)
Definition state := ident -> Z.

Definition initial_state: state := fun (x: ident) => 0.

(** Update the value of a variable, without changing the other variables. *)
Definition update (s: state) (x: ident) (n: Z) : state :=
  fun y => if eq_ident x y then n else s y.

(** Good variable properties for [update]. *)

Lemma update_same:
  forall x val m, (update m x val) x = val.
Proof.
  unfold update; intros. destruct (eq_ident x x); congruence.
Qed.

Lemma update_other:
  forall x val m y, x <> y -> (update m x val) y = m y.
Proof.
  unfold update; intros. destruct (eq_ident x y); congruence.
Qed.

(* Evaluation of expressions *)

Fixpoint aeval (s: state) (e: aexp) {struct e} : Z :=
  match e with
  | Var x => s x
  | Const n => n
  | Plus e1 e2 => aeval s e1 + aeval s e2 
  | Minus e1 e2 => aeval s e1 - aeval s e2 
  end.

Fixpoint beval (s: state) (b: bexp) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | Eq e1 e2 =>
      if Z_eq_dec (aeval s e1) (aeval s e2) then true else false
  | Le e1 e2 =>
      if Z_le_dec (aeval s e1) (aeval s e2) then true else false 
  | Not b1     => negb (beval s b1)
  | And b1 b2  => (beval s b1) && (beval s b2)
  end.

Compute (aeval initial_state (Var vx)).

Compute (
  let x : ident := 0 in
  let s : state := update initial_state x 12 in
  aeval s (Plus (Var x) (Const 1))).

(* An example of optimization of expressions 
   Write a function that transforms any arithmetic expression such as
   0 + a into a, and leave other expressions unchanged. *)
Fixpoint optimize_0plus (e:aexp) : aexp := (* TO DO ! *)

(* Check that the function optimizes the expression 2+(0+(0+1)) into 
the expression 2+1. *)

(** * 3. Small-step semantics: execution of statements *)

Inductive red: command * state -> command * state -> Prop :=
  | red_assign: forall x e s,
      red (Assign x e, s) (Skip, update s x (aeval s e))
  | red_seq_left: forall c1 c2 s c1' s',
      red (c1, s) (c1', s') ->
      red (Seq c1 c2, s) (Seq c1' c2, s')
  | red_seq_skip: forall c s,
      red (Seq Skip c, s) (c, s)
  | red_if_true: forall s b c1 c2,
      beval s b = true ->
      red (If b c1 c2, s) (c1, s)
  | red_if_false: forall s b c1 c2,
      beval s b = false ->
      red (If b c1 c2, s) (c2, s)
  | red_while_true: forall s b c,
      beval s b = true ->
      red (While b c, s) (Seq c (While b c), s)
  | red_while_false: forall b c s,
      beval s b = false ->
      red (While b c, s) (Skip, s).

(* Prove the following lemma stating that red is deterministic.   
   Use "induction 1" to reason by induction on derivations.
*)
Lemma red_deterministic:
  forall cs cs1, red cs cs1 -> forall cs2, red cs cs2 -> cs1 = cs2.
Proof.
  induction 1. 
(* TO DO ! *)
Qed.

(** * 4. Natural sematnics (big-step) *)

(** [eval m a n] is true if the expression [a] evaluates to value [n] in memory state [m]. *)

Inductive eval: state -> aexp -> Z -> Prop :=
  | eval_const: forall m n,
      eval m (Const n) n
  | eval_var: forall m x n,
      m x = n ->
      eval m (Var x) n
  | eval_plus: forall m a1 a2 n1 n2,
      eval m a1 n1 -> eval m a2 n2 ->
      eval m (Plus a1 a2) (n1 + n2)
  | eval_minus: forall m a1 a2 n1 n2,
      eval m a1 n1 -> eval m a2 n2 ->
      eval m (Minus a1 a2) (n1 - n2).

(** Prove the following example of evaluation. *)
Goal eval (update initial_state vx 42) (Plus (Var vx) (Const 2)) 44.
Proof.
(* TO DO ! *)

(** ** Boolean expressions *)

(** [beval m be bv] is true if the boolean expression [be] evaluates to the
  boolean value [bv] (either [true] or [false]) in memory state [m]. *)

Inductive beval2: state -> bexp -> bool -> Prop :=
  | beval_true: forall m,
      beval2 m TRUE true
  | beval_false: forall m,
      beval2 m FALSE false
  | beval_eq_true: forall m a1 a2 n1 n2,
      eval m a1 n1 -> eval m a2 n2 -> n1 = n2 ->
      beval2 m (Eq a1 a2) true
  | beval_eq_false: forall m a1 a2 n1 n2,
      eval m a1 n1 -> eval m a2 n2 -> n1 <> n2 ->
      beval2 m (Eq a1 a2) false
  | beval_le_true: forall m a1 a2 n1 n2,
      eval m a1 n1 -> eval m a2 n2 -> n1 <= n2 ->
      beval2 m (Le a1 a2) true
  | beval_le_false: forall m a1 a2 n1 n2,
      eval m a1 n1 -> eval m a2 n2 -> n1 > n2 ->
      beval2 m (Le a1 a2) false
  | beval_not: forall m be1 bv1,
      beval2 m be1 bv1 ->
      beval2 m (Not be1) (negb bv1)
  | beval_and: forall m be1 bv1 be2 bv2,
      beval2 m be1 bv1 -> beval2 m be2 bv2 ->
      beval2 m (And be1 be2) (bv1 && bv2).

(** [exec m c m'] is true if the command [c], executed in the initial
  state [m], terminates without error in final state [m']. *)

Inductive exec: state -> command -> state -> Prop :=
  | exec_skip: forall m,
      exec m Skip m
  | exec_assign: forall m x a,
      exec m (Assign x a) (update m x (aeval m a))
  | exec_seq: forall m c1 c2 m' m'',
      exec m c1 m' -> exec m' c2 m'' ->
      exec m (Seq c1 c2) m''
  | exec_if_true: forall m b ifso ifnot m',
      beval m b = true -> exec m ifso m' ->
      exec m (If b ifso ifnot) m'
  | exec_if_false: forall m b ifso ifnot m',
      beval m b = false -> exec m ifnot m' ->
      exec m (If b ifso ifnot) m'
  | exec_while_false: forall m b body,
      beval m b = false ->
      exec m (While b body) m
  | exec_while_true: forall m b body m' m'',
      beval m b = true -> exec m body m' -> exec m' (While b body) m'' ->
      exec m (While b body) m''.

(** Prove the following example of program execution  *)
Lemma let prog := If (Le (Const 1) (Const 2)) (Assign vx (Const 3)) (Assign vx (Const 0)) in
     exists m, exec initial_state prog m /\ m vx = 3.
Proof.
(* TO DO ! *)

(** Example of non terminating execution *)

Goal let prog := While TRUE Skip in
     forall m m', ~ exec m prog m'.
Proof.
  simpl; intros; red; intros. dependent induction H. inversion H. auto.
Qed.

(* Example of proof of equivalence between two programs. 
  In order to prove this lemma, you should need 
  several uses of inversion, but not induction. *)
Lemma equiv1 :
  forall x i m m', 
   exec m (Seq (Assign x (Const 1)) (While (Le (Var x) (Const 2)) i)) m' -> 
   exec m (Seq (Assign x (Const 1))
             (Seq i (While (Le (Var x) (Const 2)) i))) m'.
Proof.
(* TO DO *)
Admitted.

(** * 5. Small-step semantics: program execution *)

(* In the following, we use notations from the Sequences.v file. *)

Definition prog_terminates (prog: command) (m_init m_final: state) : Prop :=
  star red (prog, m_init) (Skip, m_final).

Definition prog_diverges (prog: command) (m_init: state) : Prop :=
  infseq red (prog, m_init).

Definition prog_crashes (prog: command) (m_init: state) : Prop :=
  exists c, exists m,
      star red (prog, m_init) (c, m)
   /\ irred red (c, m) /\ ~(c = Skip ).

(** * 6. Equivalence between the small-step and big-step semantics *)

(** ** Big-step -> small-step *)

Lemma star_red_seq_left:
  forall c s c' s' c2,
  star red (c, s) (c', s') ->
  star red (Seq c c2, s) (Seq c' c2, s').
Proof.
  intros. dependent induction H. constructor.
  destruct b. econstructor. apply red_seq_left; eauto. eauto. 
Qed. 

(* Prove the foloowing lemma *)
Lemma exec_terminates:
  forall m c m', exec m c m' -> prog_terminates c m m'.
Proof.
  induction 1; intros.
(* TO DO *)
Admitted.

(** ** Small-step -> big-step *)

(** The reverse implication, from small-step to big-step, is more subtle.
The key lemma is the following, showing that one step of reduction
followed by a big-step evaluation to a final state can be collapsed
into a single big-step evaluation to that final state. *)

Lemma red_preserves_exec:
  forall c1 s1 c2 s2,
  red (c1, s1) (c2, s2) ->
  forall s3,
  exec s2 c2 s3 ->
  exec s1 c1 s3.
Proof.
  intros until s2. intro STEP. dependent induction STEP; intros.
(* TO DO ! *)
Admitted.

(** As a consequence, a term that reduces to [Skip] evaluates in big-step
  with the same final state. *)

Theorem terminates_exec:
  forall m c m',
  prog_terminates c m m' ->
  exec m c m'.
Proof.
   unfold prog_terminates; intros. dependent induction H.
  apply exec_skip.
  destruct b as [m1 c1]. apply red_preserves_exec with m1 c1; auto.
Qed.
