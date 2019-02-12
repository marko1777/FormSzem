(* https://softwarefoundations.cis.upenn.edu/ *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


Definition aday : day := thursday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | _ => monday
  end.

Eval compute in next_weekday tuesday.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
  simpl.
  reflexivity.
Qed.

  Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Eval compute in negb (orb true false).

Example test_orb1: (orb true false) = true.
  simpl.
  reflexivity.
Qed.

Example left_id (b : bool) : orb false b = b.
  simpl.
  reflexivity.
Qed.

Example right_id (b : bool) : orb b false = b.
  simpl.
  intros.
  destruct b.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed.

Example komm (lhs rhs : bool) : orb lhs rhs = orb rhs lhs.
intros lhs.
destruct lhs.
  (*lhs = true *)
  simpl.
  destruct rhs.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  (* lhs = false *)
  simpl.
destruct rhs.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.
