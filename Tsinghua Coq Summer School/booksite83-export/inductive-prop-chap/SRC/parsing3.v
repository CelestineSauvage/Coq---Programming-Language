Require Export List.
Require Export Arith.
Require Export parsing2.
(* In our exercises we consider strings with only opeing and closing
  parentheses. *)
 
Inductive char : Set :=
  | open : char
  | close : char.
(* This is the definition of well-parenthesized expressions that is
  probably the easiest to agree on. solution to \ref{exo-wp-1} *)
 
Inductive wp : list char -> Prop :=
  | wp_nil : wp nil
  | wp_concat : forall l1 l2:list char, wp l1 -> wp l2 -> wp (l1 ++ l2)
  | wp_encapsulate :
      forall l:list char, wp l -> wp (open :: l ++ close :: nil).
 
Theorem wp_oc : wp (open :: close :: nil).
change (wp (open :: nil ++ close :: nil)) in |- *.
apply wp_encapsulate.
apply wp_nil.
Qed.
 
Theorem wp_o_head_c :
 forall l1 l2:list char, wp l1 -> wp l2 -> wp (open :: l1 ++ close :: l2).
intros l1 l2 H1 H2.
replace (open :: l1 ++ close :: l2) with ((open :: l1 ++ close :: nil) ++ l2).
apply wp_concat.
apply wp_encapsulate; trivial.
trivial.
repeat (simpl in |- *; rewrite app_ass); simpl in |- *.
trivial.
Qed.
 
Theorem wp_o_tail_c :
 forall l1 l2:list char,
   wp l1 -> wp l2 -> wp (l1 ++ open :: l2 ++ close :: nil).
intros l1 l2 H1 H2.
apply wp_concat.
trivial.
apply wp_encapsulate.
trivial.
Qed.
(* The structure of well-parenthesized expressions can actually be
  represented by binary trees.*)
 
Inductive bin : Set :=
  | L : bin
  | N : bin -> bin -> bin.
 
Fixpoint bin_to_string (t:bin) : list char :=
  match t with
  | L => nil (A:=char)
  | N u v => open :: bin_to_string u ++ close :: bin_to_string v
  end.
(* This is the correction for exercise \ref{exo-wp-1-1} *)
 
Theorem bin_to_string_wp : forall t:bin, wp (bin_to_string t).
simple induction t.
simpl in |- *; apply wp_nil.
simpl in |- *; intros t1 H1 t2 H2; apply wp_o_head_c; trivial.
Qed.
Hint Resolve wp_nil wp_concat wp_encapsulate wp_o_head_c wp_o_tail_c wp_oc.
 
Fixpoint bin_to_string' (t:bin) : list char :=
  match t with
  | L => nil (A:=char)
  | N u v =>
      bin_to_string' u ++ open :: bin_to_string' v ++ close :: nil
  end.
(* This is the correction for exercise \ref{exo-wp-1-2} *)
 
Theorem bin_to_string'_wp : forall t:bin, wp (bin_to_string' t).
simple induction t; simpl in |- *; auto.
Qed.
 
Inductive parse_rel : list char -> list char -> bin -> Prop :=
  | parse_node :
      forall (l1 l2 l3:list char) (t1 t2:bin),
        parse_rel l1 (close :: l2) t1 ->
        parse_rel l2 l3 t2 -> parse_rel (open :: l1) l3 (N t1 t2)
  | parse_leaf_nil : parse_rel nil nil L
  | parse_leaf_close :
      forall l:list char, parse_rel (close :: l) (close :: l) L.
(* solution to exercise \ref{exo-wp-6} *)
 
Theorem parse_rel_sound_aux :
 forall (l1 l2:list char) (t:bin),
   parse_rel l1 l2 t -> l1 = bin_to_string t ++ l2.
intros l1 l2 t H; elim H; clear H l1 l2 t.
intros l1 l2 l3 t1 t2 Hp Hr1 Hp2 Hr2.
simpl in |- *.
rewrite app_ass.
rewrite Hr1.
simpl in |- *.
rewrite Hr2.
reflexivity.
reflexivity.
intros l; reflexivity.
Qed.
 
Theorem parse_rel_sound :
 forall l:list char, ( exists t : bin , parse_rel l nil t) -> wp l.
intros l [t H]; replace l with (bin_to_string t).
apply bin_to_string_wp.
symmetry  in |- *.
replace (bin_to_string t) with (bin_to_string t ++ nil).
apply parse_rel_sound_aux.
auto.
rewrite app_nil_end; auto.
Qed.
(* This is another possible definition of well-parenthesized expressions,
  actually better adapted to showing that a given parser is correct. *)
 
Inductive wp' : list char -> Prop :=
  | wp'_nil : wp' nil
  | wp'_cons :
      forall l1 l2:list char,
        wp' l1 -> wp' l2 -> wp' (open :: l1 ++ close :: l2).
(* To prove that the two definitions of well-parenthesized expressions are
  equivalent, we need to prove that each predicate satisfies the constructors
  of the other. *)
 
Theorem wp'_concat :
 forall l1 l2:list char, wp' l1 -> wp' l2 -> wp' (l1 ++ l2).
intros l1 l2 H; generalize l2; clear l2.
elim H.
simpl in |- *; auto.
intros l1' l2' Hb1' Hr1 Hb2' Hr2 l2 Hb2.
simpl in |- *.
rewrite app_ass.
simpl in |- *.
apply wp'_cons; auto.
Qed.
Hint Resolve wp'_nil wp'_cons wp'_concat.
(* This is the other constructor of wp, also satisfied by wp'. *)
 
Theorem wp'_encapsulate :
 forall l:list char, wp' l -> wp' (open :: l ++ close :: nil).
intros l H; elim H; auto.
Qed.
(* One interpretation of inductive definitions of predicate is that
  the defined predicate is the least (with respect to implication) to
  satisfy the constructors.  Thus, having proved that one of the predicates
  satisfies the constructors of the other gives a simple way to prove
  that one predicate implies the other.  The proof is done by induction
  on the predicate. solution to \ref{exo-wp-2}*)
 
Theorem wp_imp_wp' : forall l:list char, wp l -> wp' l.
intros l H; elim H.
apply wp'_nil.
intros; apply wp'_concat; trivial.
intros; apply wp'_encapsulate; trivial.
Qed.
 
Theorem wp'_imp_wp : forall l:list char, wp' l -> wp l.
intros l H; elim H; auto.
Qed.
(* Here is an alternative definition, the same as before, but with the
  second constructor that privileges parentheses on the right. *)
 
Inductive wp'' : list char -> Prop :=
  | wp''_nil : wp'' nil
  | wp''_cons :
      forall l1 l2:list char,
        wp'' l1 -> wp'' l2 -> wp'' (l1 ++ open :: l2 ++ close :: nil).
(* We plan to make much more proofs automatically about this one. *)
Hint Resolve wp''_nil wp''_cons.
(* Obviously this one also satisfies the concatenation property. *)
 
Lemma wp''_concat :
 forall l1 l2:list char, wp'' l1 -> wp'' l2 -> wp'' (l1 ++ l2).
(* Only a proof by induction on the fact that the second list is well-parenthesized
  is needed. *)
intros l1 l2 H1 H2; generalize l1 H1; clear H1 l1.
elim H2.
intros; rewrite <- app_nil_end; trivial.
intros; rewrite ass_app; auto.
Qed.
 
Theorem wp''_encapsulate :
 forall l:list char, wp'' l -> wp'' (open :: l ++ close :: nil).
intros l H; change (wp'' (nil ++ open :: l ++ close :: nil)) in |- *.
auto.
Qed.
Hint Resolve wp''_concat wp''_encapsulate.
(* solution to exercise \ref{exo-wp-4} *)
 
Theorem wp_imp_wp'' : forall l:list char, wp l -> wp'' l.
simple induction 1; auto.
Qed.
 
Theorem wp''_imp_wp : forall l:list char, wp'' l -> wp l.
simple induction 1; auto.
Qed.
 
Fixpoint recognize (n:nat) (l:list char) {struct l} : bool :=
  match l with
  | nil => match n with
           | O => true
           | _ => false
           end
  | open :: l' => recognize (S n) l'
  | close :: l' => match n with
                   | O => false
                   | S n' => recognize n' l'
                   end
  end.
(* solution to exercise \ref{exo-wp-4} *)
 
Theorem recognize_complete_aux :
 forall l:list char,
   wp l ->
   forall (n:nat) (l':list char), recognize n (l ++ l') = recognize n l'.
intros l H; elim H.
simpl in |- *; auto.
intros l1 l2 H1 Hrec1 H2 Hrec2 n l'.
rewrite app_ass; transitivity (recognize n (l2 ++ l')); auto.
intros l1 H1 Hrec n l'; simpl in |- *; rewrite app_ass; rewrite Hrec;
 simpl in |- *; auto.
Qed.
 
Theorem recognize_complete : forall l:list char, wp l -> recognize 0 l = true.
intros l H; rewrite (app_nil_end l); rewrite recognize_complete_aux; auto.
Qed.
 
Theorem app_decompose :
 forall (A:Set) (l1 l2 l3 l4:list A),
   l1 ++ l2 = l3 ++ l4 ->
   ( exists l1' : list A , l1 = l3 ++ l1' /\ l4 = l1' ++ l2) \/
   ( exists a : A,
     ( exists l2' : list A , l3 = l1 ++ a :: l2' /\ l2 = (a :: l2') ++ l4)).
simple induction l1.
intros l2 l3; case l3.
intros l4 H; left; exists (nil (A:=A)); auto.
intros a l3' Heq; right; exists a; exists l3'; auto.
clear l1; intros a l1 Hrec l2 l3; case l3.
intros l4 H; left; exists (a :: l1); auto.
simpl in |- *; intros a' l3' l4 Heq; injection Heq; intros Heq' Heq''.
elim Hrec with (1 := Heq').
intros [l1' [Heq3 Heq4]]; left; exists l1'; split; auto.
rewrite Heq''; rewrite Heq3; auto.
intros [a'' [l2' [Heq3 Heq4]]]; right; exists a''; exists l2'; split; auto.
rewrite Heq''; rewrite Heq3; auto.
Qed.
(* length of lists is actually an abstract view of lists.  There is
  a morphism between appending and addition.  This is already visible
  in the structure of the two functions app and plus and the proof of
  this theorem follows in a simple way the structure of app (and plus by
  the same occasion). *)
 
Theorem length_app :
 forall (A:Set) (l1 l2:list A), length (l1 ++ l2) = length l1 + length l2.
simple induction l1; simpl in |- *; auto.
Qed.
 
Theorem length_rev : forall (A:Set) (l:list A), length l = length (rev l).
simple induction l; auto.
intros a l' H; simpl in |- *.
rewrite length_app.
simpl in |- *; rewrite <- plus_n_Sm; rewrite H; auto with arith.
Qed.
 
Theorem cons_to_app_end :
 forall (A:Set) (l:list A) (a:A),
    exists b : A , ( exists l' : list A , a :: l = l' ++ b :: nil).
intros A l a.
rewrite <- (rev_involutive (a :: l)).
(* We want to use the first element of (rev (cons a l)) but we
  need to say that this list has at least one element. *)
cut (0 < length (rev (a :: l))).
case (rev (a :: l)).
(* If (rev (cons a l)) was nil, then there would be a contradiction. *)
simpl in |- *; intros H'; elim (lt_n_O 0); auto.
intros b l'; exists b; exists (rev l'); simpl in |- *; auto.
(* Now we need to show that the reversed list has more than one element *)
rewrite <- length_rev; simpl in |- *; auto with arith.
Qed.
 
Theorem last_same :
 forall (A:Set) (a b:A) (l1 l2:list A),
   l1 ++ a :: nil = l2 ++ b :: nil -> l1 = l2 /\ a = b.
intros A a b l1 l2 H.
cut (a :: rev l1 = b :: rev l2).
intros H'; injection H'; intros H1 H2; split; auto.
rewrite <- (rev_involutive l1).
rewrite H1.
apply rev_involutive.
repeat rewrite <- rev_unit.
rewrite H; auto.
Qed.
 
Theorem wp_remove_oc_aux :
 forall l:list char,
   wp l ->
   forall l1 l2:list char, l1 ++ l2 = l -> wp (l1 ++ open :: close :: l2).
intros l H; elim H.
(* In the first case l is the empty list, there is only one way to insert
  an open-string pair.  We use the theorem app_eq_nil to determine
  l1 and l2.  This theorem has implicit arguments. *)
intros l1 l2 H1; elim (app_eq_nil _ _ H1); auto.
simpl in |- *; intros Heq1 Heq2; rewrite Heq1; rewrite Heq2; apply wp_oc.
(* In the second case l is already a concatenation of two well-parenthesized
   expressions l1 and l2.  We need to now whether the open-close pair is
  inserted in l1' or in l2', the theorem app_decompose helps here. *)
intros l1 l2 Hp1 Hr1 Hp2 Hr2 l3 l4 Heq.
elim app_decompose with (1 := Heq).
intros [l1' [Heq1 Heq2]].
rewrite Heq1.
rewrite app_ass.
apply wp_concat; auto.
intros [a' [l2' [Heq1 Heq2]]].
rewrite Heq2.
repeat rewrite app_comm_cons.
rewrite ass_app.
apply wp_concat; auto.
(* In the third case, we haev to check three possibilities: either
   the open-close pair has been inserted before the existing open character,
  or between the two parentheses, or after. *)
idtac.
intros l' Hp'' Hrec l1; case l1.
simpl in |- *; intros l2 Heq; rewrite Heq.
change (wp (open :: nil ++ close :: open :: l' ++ close :: nil)) in |- *;
 auto.
simpl in |- *; intros c l1' l2; case l2.
(* If l2 is nil, then the open-close pair was introduced after the
  closing parenthesis. *)
intros Heq; injection Heq; intros Heq1 Heq2.
rewrite <- app_nil_end in Heq1; rewrite Heq1; rewrite Heq2.
rewrite app_comm_cons.
apply wp_concat; auto.
(* if l2 is non nil then the open-close pair was introduced between the
  parentheses *)
intros c' l2'.
elim (cons_to_app_end char l2' c').
intros c'' [l2'' Heq]; rewrite Heq.
rewrite ass_app; intros Heq1.
injection Heq1; intros Heq2 Heq3.
elim last_same with (1 := Heq2).
intros Heq4 Heq5; rewrite Heq5; rewrite Heq3.
change (wp (open :: l1' ++ (open :: close :: l2'') ++ close :: nil)) in |- *.
rewrite ass_app; auto.
Qed.
 
Theorem wp_remove_oc :
 forall l1 l2:list char, wp (l1 ++ l2) -> wp (l1 ++ open :: close :: l2).
intros; apply wp_remove_oc_aux with (l := l1 ++ l2); auto.
Qed.
 
Fixpoint make_list (A:Set) (a:A) (n:nat) {struct n} : 
 list A := match n with
           | O => nil (A:=A)
           | S n' => a :: make_list A a n'
           end.
 
Theorem make_list_end :
 forall (A:Set) (a:A) (n:nat) (l:list A),
   make_list A a (S n) ++ l = make_list A a n ++ a :: l.
simple induction n; simpl in |- *.
trivial.
intros n' H l; rewrite H; trivial.
Qed.
(* Now we want to express that only well-parenthesized expressions are accepted.  Again,
  we prove a more general statement, where n is understood as the number of
  unmatched opening parentheses recognized so far. *)
 
Theorem recognize_sound_aux :
 forall (l:list char) (n:nat),
   recognize n l = true -> wp (make_list _ open n ++ l).
simple induction l; simpl in |- *.
intros n; case n.
simpl in |- *; intros; apply wp_nil.
intros n' H; discriminate H.
intros a; case a; simpl in |- *; clear a.
intros l' H n H0.
rewrite <- make_list_end; auto.
intros l' H n; case n; clear n.
intros H'; discriminate H'.
intros n H0.
rewrite make_list_end.
apply wp_remove_oc.
auto.
Qed.
(* The soundness statement is the general statement specialized to value 0.
  solution to exercise \ref{exo-wp-5} *)
 
Theorem recognize_sound : forall l:list char, recognize 0 l = true -> wp l.
intros l H; generalize (recognize_sound_aux _ _ H).
simpl in |- *; auto.
Qed.
(* Now we want to write a real parser, that is, a function that constructs a term
  representing the structure of the string.
  The parsing function is a tail-recursive representation of a stack automaton.
   The argument s is the stack, the argument t is the tree representing the
  the last well-formed expression that was recognized.  The return value is
  None if the string is rejected and (Some t) if the string is accepted.  In
  this case one should be able to reconstruct the recognized string from t,
  but this is done later as another exercise. *)
 
Fixpoint parse (s:list bin) (t:bin) (l:list char) {struct l} : 
 option bin :=
  match l with
  | nil => match s with
           | nil => Some t
           | _ => None (A:=bin)
           end
  | open :: l' => parse (t :: s) L l'
  | close :: l' =>
      match s with
      | t' :: s' => parse s' (N t' t) l'
      | _ => None (A:=bin)
      end
  end.
(* The length of the stack plays the same role as argument n in the
  function recognize. *)
 
Theorem parse_reject_indep_t :
 forall (l:list char) (s:list bin) (t:bin),
   parse s t l = None ->
   forall (s':list bin) (t':bin),
     length s' = length s -> parse s' t' l = None.
simple induction l.
intros s; case s.
simpl in |- *.
intros t H; discriminate H.
intros t0 s0 t H s'; case s'.
simpl in |- *; intros t' Hle; discriminate Hle.
simpl in |- *; auto.
intros a; case a; simpl in |- *; clear a; intros l' Hrec s.
intros t H s' t' Hle.
apply Hrec with (1 := H).
simpl in |- *; auto with arith.
case s.
intros t H s'; case s'; simpl in |- *.
auto.
intros t0 s0 t' Hle; discriminate Hle.
intros t0 s0 t H s'; case s'; simpl in |- *.
intros t' H0; discriminate H0.
intros t'0 s'0 t' Hle; apply Hrec with (1 := H).
simpl in Hle; auto with arith.
Qed.
(* Rejected strings are those for which the return value is None. 
  In the completeness theorem we actually talk about the rejected strings.
  Here it is more convenient to use wp' as the definition of well-parenthesized
  expressions to organize the proof.*)
 
Theorem parse_complete_aux :
 forall l:list char,
   wp' l ->
   forall (s:list bin) (t:bin) (l':list char),
     parse s t (l ++ l') = None ->
     forall (s':list bin) (t':bin),
       length s' = length s -> parse s' t' l' = None.
simple induction 1.
simpl in |- *; intros; eapply parse_reject_indep_t; eauto.
intros l1 l2 Hp1 Hr1 Hp2 Hr2 s t l' Hrej s' t' Hle.
apply Hr2 with (s := s') (t := N t L).
change (parse (t :: s') L (close :: l2 ++ l') = None) in |- *.
simpl in Hrej.
rewrite app_ass in Hrej.
apply Hr1 with (1 := Hrej).
simpl in |- *; auto with arith.
auto.
Qed.
 
Theorem parse_complete : forall l:list char, wp l -> parse nil L l <> None.
intros.
replace l with (l ++ nil).
red in |- *; intros H'.
cut (parse nil L nil = None).
simpl in |- *; discriminate.
apply parse_complete_aux with (2 := H'); auto.
apply wp_imp_wp'; auto.
rewrite <- app_nil_end; auto.
Qed.
(* We will use bin_to_string' to map binary trees to strings of characters.
  Stacks also represent strings. *)
 
Fixpoint unparse_stack (s:list bin) : list char :=
  match s with
  | nil => nil (A:=char)
  | t :: s' => unparse_stack s' ++ bin_to_string' t ++ open :: nil
  end.
 
Theorem parse_invert_aux :
 forall (l:list char) (s:list bin) (t t':bin),
   parse s t l = Some t' ->
   bin_to_string' t' = unparse_stack s ++ bin_to_string' t ++ l.
simple induction l.
intros s; case s.
simpl in |- *.
intros t t' H; injection H; intros Heq.
rewrite Heq; apply app_nil_end.
simpl in |- *; intros t0 s0 t t' H; discriminate H.
intros a; case a; simpl in |- *; clear a; intros l' Hrec s.
intros t t' H.
rewrite Hrec with (1 := H).
simpl in |- *.
repeat (rewrite app_ass; simpl in |- *).
auto.
case s.
intros t t' H; discriminate H.
intros t0 s0 t t' Hp; rewrite Hrec with (1 := Hp).
simpl in |- *.
repeat (rewrite app_ass; simpl in |- *).
auto.
Qed.
 
Theorem parse_invert :
 forall (l:list char) (t:bin), parse nil L l = Some t -> bin_to_string' t = l.
intros; replace l with (unparse_stack nil ++ bin_to_string' L ++ l); auto.
apply parse_invert_aux; auto.
Qed.
(* With this last theorem, we know that our parser is correct, that is
  sound and complete. *)
 
Theorem parse_sound :
 forall (l:list char) (t:bin), parse nil L l = Some t -> wp l.
intros l t H; rewrite <- parse_invert with (1 := H).
apply bin_to_string'_wp.
Qed.
(* Now, an exercise for which we do not give the solution is the exercise
          where strings can also contain other characters that play no role with
          respect to parentheses, but should not be forgotten by the parser.*)