(* BEGIN FIX *)
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (n1 n2 : nat)
  | BGe (n1 n2 : nat)
  | BNot (b : bexp)
  | BOr (b1 b2 : bexp).

From Coq Require Import Init.Nat.

Eval compute in 3 =? 4.
Eval compute in 3 <=? 3.

Fixpoint beval (b : bexp) : bool := 
(* END FIX *)
  match b with
    | BTrue => true
    | BFalse => false
    | BEq n1 n2 => n1 =? n2
	  | BGe n1 n2 => negb (n1 <? n2)
	  | BNot b => negb (beval b)
	  | BOr b1 b2 => orb (beval b1) (beval b2)
end.

(* BEGIN FIX *)
Example beval_test_1 : beval (BGe 3 4) = false.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Example beval_test_2 : beval (BGe 3 3) = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Example beval_test_3 : beval (BGe 5 3) = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Example beval_test_4 : beval (BOr (BGe 3 4) (BGe 3 2)) = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Definition BAnd (b1 b2 : bexp) : bexp := 
(* END FIX *)
  BNot(BOr (BNot b1) (BNot b2))
.
(* BEGIN FIX *)
Example beval_test_5 : beval (BAnd (BGe 3 4) (BGe 3 2)) = false.
(* END FIX *)
simpl. reflexivity.
Qed.

(* BEGIN FIX *)
Example beval_test_6 : beval (BAnd (BGe 4 4) (BGe 3 2)) = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Example beval_test_7 : beval
  (BAnd
    (BOr
      (BOr
        (BNot BTrue)
        (BEq 3 3))
      (BGe 5 3))
    (BNot (BEq 3 4)))
  = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Lemma bor_left_unit (b : bexp) : beval (BOr BFalse b) = beval b.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Lemma lem (b : bexp)(p : beval b = true) : beval (BAnd b BTrue) = true.
(* END FIX *)
simpl.
rewrite -> p.
simpl.
reflexivity.
Qed.
