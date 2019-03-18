(* BEGIN FIX *)

Definition name : Type := nat.
Definition state : Type := name -> nat.

Inductive aexp : Type :=
  | Num : nat -> aexp
  | Var : name -> aexp
  | Add : aexp -> aexp -> aexp
  | Mul : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | True : bexp
  | False : bexp
  | Not : bexp -> bexp
  | And : bexp -> bexp -> bexp
  | Eq  : aexp -> aexp -> bexp.

Definition W : name := 1.
Definition X : name := 2.
Definition Y : name := 3.
Definition Z : name := 4.

(* N.B. negb : bool -> bool, andb : bool -> bool -> bool *)

Fixpoint aeval (e : aexp)(s : state) : nat :=
(* END FIX *)
  match e with
  | Num a => a 
  | Var v => s v
  | Add a b => aeval a s + aeval b s
  | Mul a b => aeval a s * aeval b s
end.
(* BEGIN FIX *)

(* N.B. Nat.eqb : Nat -> Nat -> Bool *)

Fixpoint beval (e : bexp)(s : state) : bool :=
(* END FIX *)
  match e with
  | True => true
  | False => false
  | Not a => negb (beval a s)
  | And a b => andb (beval a s) (beval b s)
  | Eq a b => Nat.eqb (aeval a s) (aeval b s)
end.

(* BEGIN FIX *)
Definition empty : state := fun x => 0.

Definition update (x : name)(n : nat)(s : state)
 : state := fun x' => if Nat.eqb x x' then n else s x'.

Example ex1 : beval (And (Not False) (Eq (Var W) (Num 0))) empty = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Example ex2 : beval (And (Not (Not (And True False))) (Eq (Num 3) (Num 3))) (fun _ => 133) = false.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Example ex3 : beval (Eq (Mul (Num 3) (Num 2)) (Add (Num 1) (Num 5))) empty = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)
Definition exState : state :=
(* END FIX *)
update W 0 (update Z 1 empty).

(* BEGIN FIX *)
Lemma l_ex : beval (And (Not (Not (Eq (Var W) (Num 0)))) (Eq (Var Z) (Num 1))) exState = true.
(* END FIX *)
simpl. reflexivity. Qed.

(* BEGIN FIX *)

Lemma eqb_refl (n : nat) : Nat.eqb n n = true.
induction n. reflexivity. simpl. rewrite -> IHn. reflexivity. Qed.

(* let's show that updating in a different order results in the same value 

use unfold instead of simpl!

*)

Lemma l_update (x y : name)(xy : Nat.eqb y x = false)(n m : nat)(s : state) :
  (update x n (update y m s)) x = (update y m (update x n s)) x.
(* END FIX *)
unfold update. rewrite -> xy. rewrite -> eqb_refl. reflexivity. Qed.
