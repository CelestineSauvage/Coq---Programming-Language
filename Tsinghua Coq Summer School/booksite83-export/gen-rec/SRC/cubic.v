Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export Wf_nat.
 
Definition div8_spec:
 forall n,  ({q : nat & {r : nat | n = 8 * q + r /\ r < 8}}).
refine (fix
        div8 (n : nat) : {q : nat & {r : nat | n = 8 * q + r /\ r < 8}} :=
           match n return {q : nat & {r : nat | n = 8 * q + r /\ r < 8}} with
              S (S (S (S (S (S (S (S x))))))) =>
                match div8 x with existS q' (exist r (conj Heq Hlt)) => _ end
             | _ => _
           end).
exists 0; exists 0; omega.
exists 0; exists 1; omega.
exists 0; exists 2; omega.
exists 0; exists 3; omega.
exists 0; exists 4; omega.
exists 0; exists 5; omega.
exists 0; exists 6; omega.
exists 0; exists 7; omega.
exists (S q'); exists r; omega.
Qed.
(* We use a different inequality to express that the cubic root we provide is
  not an underestimation, but we will produce a more intuitive specification
  in the final function.  The specication we use here should make the proofs by
  omega easier. *)
 
Definition cubic_F:
 forall n,
 (forall y,
  y < n ->
   ({s : nat & {r : nat | y = (s * s) * s + r /\ r <= 3 * (s * s) + 3 * s}})) ->
  ({s : nat & {r : nat | n = (s * s) * s + r /\ r <= 3 * (s * s) + 3 * s}}).
refine (fun n cubic =>
           match div8_spec n with
             existS (S q) (exist r8 (conj Heq Hltr8)) =>
               match cubic (S q) _ with
                 existS c' (exist r (conj Heqc Hltr)) =>
                   match le_lt_dec ((12 * (c' * c') + 6 * c') + 1) (8 * r + r8)
                    with left Hle => _ | right Hlt => _ end
               end
            | existS 0 (exist 0 (conj Heq _)) => _
            | existS 0 (exist (S n') (conj Heq Hlt)) => _
           end).
exists 0; exists 0; rewrite Heq; omega.
exists 1; exists n'; rewrite Heq; omega.
omega.
exists (2 * c' + 1); exists ((8 * r + r8) - ((12 * (c' * c') + 6 * c') + 1)).
rewrite Heq.
replace
 (((2 * c' + 1) * (2 * c' + 1)) * (2 * c' + 1) +
  ((8 * r + r8) - ((12 * (c' * c') + 6 * c') + 1)))
     with
      (((8 * c') * c') * c' +
       (((12 * (c' * c') + 6 * c') + 1) +
        ((8 * r + r8) - ((12 * (c' * c') + 6 * c') + 1)))).
rewrite le_plus_minus_r.
rewrite Heqc.
split.
ring.
apply plus_le_reg_l with ((12 * (c' * c') + 6 * c') + 1).
rewrite le_plus_minus_r.
replace ((2 * c' + 1) * (2 * c' + 1)) with ((4 * (c' * c') + 4 * c') + 1).
omega.
ring.
exact Hle.
exact Hle.
ring.
exists (2 * c'); exists (8 * r + r8); split.
rewrite Heq; rewrite Heqc; ring.
replace ((2 * c') * (2 * c')) with (4 * (c' * c')).
omega.
ring.
Qed.
 
Definition cubic:
 forall n,
  ({c : nat &
   {r : nat | n = (c * c) * c + r /\ n < ((c + 1) * (c + 1)) * (c + 1)}}).
intros n;
 elim
  (well_founded_induction
    lt_wf
    (fun n =>
     {c : nat & {r : nat | n = (c * c) * c + r /\ r <= 3 * (c * c) + 3 * c}})
    cubic_F n).
intros c [r [Heq Hle]].
exists c; exists r; split; trivial.
replace (((c + 1) * (c + 1)) * (c + 1))
     with ((((c * c) * c + 3 * (c * c)) + 3 * c) + 1).
omega.
ring.
Qed.
