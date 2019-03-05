Inductive aexp : Type :=
  | ANum (n : nat)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | APlus (a1 a2 : aexp)
.

Coercion ANum : nat >-> aexp.

Definition t : aexp :=
  APlus
    (AMinus
      3
      2)
     5.


(*Set Coercion on/Unset Coercion off*)
Unset Printing Coercions.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | AMinus a1 a2 => aeval a1 - aeval a2
  | AMult a1 a2 => aeval a1 * aeval a2
end.

Eval compute in aeval t.
Eval compute in aeval (APlus 5000 5000).

Fixpoint optim (a : aexp) : aexp :=
  match a with
   | ANum n => n
   | APlus a1 0 => optim(a1)
   (*| APlus 0 a2 => optim(a2)*)
   | APlus a1 a2 => APlus (optim a1) (optim a2)
   | AMinus a1 a2 => AMinus (optim a1) (optim a2)
   | AMult a1 a2 => AMult (optim a1) (optim a2)
end.

Eval compute in optim (optim (APlus 0 (APlus 0 0))).

Lemma optim_sound (a : aexp) :
  aeval (optim a) = aeval a.
 intros.
  induction a; try (simpl; reflexivity);
  try (simpl; rewrite -> IHa1;  rewrite -> IHa2; reflexivity). 
  simpl.
  destruct a2;
  try (destruct n; simpl; rewrite -> IHa1; trivial);
(*assert(aeval a1 + 0 = aeval a1). trivial helyett*)
try (simpl; rewrite -> IHa1; simpl in IHa2; rewrite -> IHa2; reflexivity).
Qed.

Fixpoint optim2 (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n 
  | APlus (ANum n) (ANum m) => ANum (n + m)
  | APlus a1 a2 => APlus (optim2 a1) (optim2 a2)
  | AMinus a1 a2 => AMinus (optim2 a1) (optim2 a2)
  | AMult a1 a2 => AMult (optim2 a1) (optim2 a2)
end.

Lemma optim_2 (a : aexp) : aeval (optim2 a) = aeval a.
 intros.
 induction a;
 try(simpl; reflexivity); 
 try(simpl; rewrite -> IHa1; rewrite -> IHa2; reflexivity).
 simpl. destruct a1. destruct a2. simpl. reflexivity. simpl. simpl in IHa2. rewrite -> IHa2. reflexivity.
simpl. reflexivity. simpl. destruct n;
try (simpl; simpl in IHa2; rewrite <- IHa2; reflexivity);
simpl. rewrite ->IHa2. simpl in IHa2. rewrite -> IHa1. 
