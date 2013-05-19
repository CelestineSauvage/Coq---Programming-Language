 Require Import Bvector.


 Implicit Arguments Vcons [A n].
 Implicit Arguments Vnil [A].
 Implicit Arguments Vhead [A n].
 Implicit Arguments Vtail [A n].

Set Implicit Arguments.

Definition vec2 (A:Type) := vector A 2.


Definition vcons2 (A:Type)(a b:A): vec2 A := Vcons a (Vcons b Vnil).

Implicit Arguments vcons2 [A].


(* we want to coerce any A-vector of length 2 into A*A
*)

 
Definition v2prod {A:Type}(v:vec2 A):(prod A A) :=
     (Vhead v, (Vhead(Vtail v))).


Lemma v2prod_ok : forall A (a b:A), v2prod  (vcons2 a b)=(a,b).
 Proof.
  reflexivity.
Qed.




Coercion v2prod : vec2 >-> prod.




Check (fst (vcons2 3 4)). 

Eval compute in (snd (vcons2 3 4)).





Definition Vid: forall (A:Type)(n:nat), vector A n -> vector A n.
 destruct n. intro v.
 exact Vnil.
 intro v; exact (Vcons (Vhead v) (Vtail v)).
Defined.





 Lemma Vid_eq : forall A n (v:vector A n), v= Vid  v.
 Proof.
  destruct v; reflexivity.
Qed.

Lemma V0 : forall A (v:vector A 0), v=Vnil.
Proof.
 intros A v.
 change (@Vnil A) with (Vid v).
 apply Vid_eq.
Qed.

Lemma VS : forall A n (v:vector A (S n)), v = Vcons (Vhead v) (Vtail v).
Proof.
 intros A n v.
 change (Vcons (Vhead v) (Vtail v)) with (Vid  v).
 apply Vid_eq.
Qed.

Lemma V2_0 : forall A (v:vec2 A), v =  vcons2 (Vhead v) (Vhead (Vtail v)). 
Proof.
 intros A v.
 pattern v at 1; rewrite  (VS  v).
 pattern (Vtail v) at 1; rewrite (VS (Vtail v)).
 unfold vcons2;rewrite <- (V0  (Vtail (Vtail v))).
 reflexivity.
Qed.

Lemma V2 : forall A (v:vec2 A), v= vcons2 (fst v) (snd v).
Proof.
 intros A v.
 generalize (V2_0 v).
 simpl.
 auto.
Qed.









 
