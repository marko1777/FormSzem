Example test (b1 :bool) : true = true.
Admitted.

(*https://people.inf.elte.hu/akaposi/fsz/*)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false=> false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (andb x y)
  (at level 50, left associativity).

Example negneg (b : bool) : negb (negb b) = b.
intros c.
destruct c.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.
(* More basic tactics computer foundation *)

Inductive Nat : Type := 
  | O : Nat
  | S : Nat -> Nat.

Definition isOne (n : Nat) : bool :=
  match n with
  | O => false
  | S O => true
  | _ => false
  end.

Definition four : Nat := S (S (S (S O))).
Definition six : Nat := S(S four).
Eval compute in isOne four.
Eval compute in isOne O.
Eval compute in isOne (S O).

(* Sn * 2 = (1 + n) * 2 = 2 + 2n *) 
(* Fixpoint For recursive definiton*)
Fixpoint twice (n : Nat) : Nat :=
 match n with
 | O => O
 | S n => S(S (twice n))
end.

Eval compute in twice six.
(* S n must be less then f n (or swapped :) ) *)
Fixpoint f (n :Nat) : Nat := match n with
 | O => O
 | S n => f n
 end.

(* Fixpoint f (n : Nat) : Nat := f n.*)

(* 
  S(S (S O)) + m 
  S(S(S O) + m) = <- S n' + m = S(n'+m)
  S(S(S O + m)) =
  S(S(S(O+m))) = <- O + m = m
  S(S(S(M)))
 *)
Fixpoint plus (n m : Nat) {struct n}  : Nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Eval compute in plus (twice six) (twice four).

Notation "x + y" := (plus x y)
  (at level 50, left associativity).

Lemma leftid (n : Nat) : O + n = n.
simpl.
reflexivity.
Qed.

Lemma rightid (n : Nat) : n + O = n.
simpl.
induction n as [|m H].
reflexivity.
simpl.
(* swap m + O to m // <- swap m to m + O*)
rewrite -> H.
reflexivity.
Qed.
(* profe associativity for NAT*)
