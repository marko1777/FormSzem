(* BEGIN FIX *)
Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Fixpoint plus (n m : Nat) {struct n} : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "n + m" := (plus n m)
  (at level 50, left associativity).

Fixpoint mul (n m : Nat) {struct n} : Nat
(* END FIX *)
 := match n with
 | O => O
 | S O => m
 | S n' => (plus m (mul n' m))
end.

(* BEGIN FIX *)
Notation "n * m" := (mul n m)
  (at level 40, left associativity).

Example mul_test_1 : S (S O) * S O = S (S O).
(* END FIX *)
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Example mul_test_2 : S (S O) * S (S (S O)) = S (S (S (S (S (S O))))).
(* END FIX *)
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Example mul_test_3 : S (S O) * O = O.
(* END FIX *)
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Example mul_test_4 : O * S (S O) = O.
(* END FIX *)
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Lemma assoc (n m o : Nat) : n + (m + o) = (n + m) + o.
(* END FIX *)
