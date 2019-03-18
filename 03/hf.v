(* BEGIN FIX *)
Fixpoint max (n m : nat) {struct n} : nat :=
  match n, m with
  | 0 , _ => m
  | S n' , 0 => n
  | S n' , S m' => S (max n' m')
  end.

Example max_test1 : max 100 200 = 200. simpl. reflexivity. Qed.
Example max_test2 : max 3 3 = 3. simpl. reflexivity. Qed.
Example max_test3 : max 4 3 = 4. simpl. reflexivity. Qed.

Inductive Tree : Type :=
  | Leaf : Tree
  | Node2 : Tree -> Tree -> Tree
  | Node3 : Tree -> Tree -> Tree -> Tree.

Definition exTree1 : Tree := Node2 (Node3 Leaf Leaf Leaf) Leaf.

Definition exTree2 : Tree := Node2 (Node2 Leaf (Node2 (Node2 Leaf Leaf) Leaf)) (Node2 Leaf Leaf).

Fixpoint height (t : Tree) {struct t} : nat :=
(* END FIX *)
 match t with
  | Leaf => 0
  | Node2 t1 t2 => 1 + (max (height t1) (height t2))
  | Node3 t1 t2 t3 => 1 + max (max (height t1) (height t2)) (height t3)
end.

(* BEGIN FIX *)
Example height_test_1 : height exTree1 = 2.
(* END FIX *)
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Example height_test_2 : height exTree2 = 4.
(* END FIX *)
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Lemma max_0 (m : nat) : max m 0 = m.
(* END FIX *)
simpl.
induction m as [|m H].
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

(* BEGIN FIX *)
Lemma height_Leaf (t : Tree) : height (Node2 t Leaf) = height (Node2 Leaf t).
(* END FIX *)
simpl.
rewrite -> max_0.
reflexivity.
Qed.

(* BEGIN FIX *)
Lemma max_comm : forall (m n : nat),  max m n = max n m.
(* END FIX *)
induction m as[|m' H].
intros.
rewrite -> max_0.
simpl.
reflexivity.
intros.
simpl.
induction n as [|n' H2].
simpl.
reflexivity.
simpl.
rewrite -> H.
reflexivity.
Qed.