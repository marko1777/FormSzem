Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.


Fixpoint plus (n m : Nat) {struct n} : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma assoc (a b c : Nat) : a + (b + c) = a + b +c.
induction a as [|a' H].
simpl.
reflexivity.
simpl.
intros b c.
rewrite -> H.
reflexivity.
Qed.

Lemma assoc (a b c : Nat) : a + (b + c) = a + b +c.
induction a as [|a' H].
simpl.
reflexivity.
simpl.
intros b c.
rewrite -> H.
reflexivity.
Qed.

Lemma rightid (n : Nat) : n + O = n.
intros n.
simpl.
induction n as [|m H].
reflexivity.
simpl.
rewrite -> H.
reflexivity.
Qed.

Lemma seged (a b : Nat) : S a + b = a + S b.
induction a as [| a' H].
simpl.
reflexivity.
intros.
simpl.
rewrite <- H.
simpl.
reflexivity.
Qed.

Lemma comm (a b : Nat) : a + b = b + a.
induction a as [| a' H].
intros.
rewrite -> rightid.
simpl.
reflexivity.
intros.
induction b.
simpl.
rewrite -> rightid.
reflexivity.
simpl.
rewrite <- IHb.
rewrite -> seged.
reflexivity.
Qed.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition ex : aexp := 
 APlus 
 (
  AMult
   (APlus (ANum 1) (ANum 2)) 
   (ANum 3)
 ) 
 (
   AMinus 
   (ANum 4) 
   (ANum 5)
 ).
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.

Fixpoint leafCount (e :aexp) {struct e} : nat :=
 match e with
 | ANum x => 1
 | APlus e1 e2 => leafCount(e1) + leafCount(e2)
 | AMinus e1 e2 => leafCount(e1) + leafCount(e2)
 | AMult e1 e2 => leafCount(e1) + leafCount(e2)
end.

Eval compute in leafCount ex.

(* wtf Eval compute in ((ANum 1) + (ANum 2)). *)

Lemma leafs (e : aexp) : 
  leafCount (APlus e (ANum 1)) =
  leafCount (APlus (ANum 1) e).
intros.
simpl.
induction e.
simpl.
reflexivity.
simpl.
rewrite IHe1. 



Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


