(* BEGIN FIX *)
Require Import Coq.Strings.String.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (x : string)
  | APlus (a a' : aexp)
  | AMult (a a' : aexp).

Definition state : Type := string -> nat.

Fixpoint aeval (e : aexp)(s : state) : nat := match e with
  | ANum n => n
  | AVar x => s x
  | APlus a a' => aeval a s + aeval a' s
  | AMult a a' => aeval a s * aeval a' s
  end.

Inductive zart : aexp -> Prop :=
  | szam (n : nat) : zart (ANum n)
  | osszeg (a a' : aexp)(az : zart a)
           (a'z : zart a') : zart (APlus a a')
  | szorzat (a a' : aexp)(az : zart a)
            (a'z : zart a') : zart (AMult a a').


Example pl1 : zart (APlus (ANum 3) (ANum 4)).
(* END FIX *)
apply osszeg; apply szam. Qed.

(* BEGIN FIX *)
Example pl3 : zart (APlus (ANum 3) 
                          (AMult (ANum 1) (ANum 2))).
(* END FIX *)
apply osszeg. apply szam. apply szorzat; apply szam. Qed.

(* BEGIN FIX *)
Theorem zartEval (e : aexp)(s s' : state)(p : zart e) :
  aeval e s = aeval e s'.
(* p-n vegezz indukciot! *)
(* END FIX *)
induction p. simpl. reflexivity. simpl. rewrite -> IHp1. rewrite -> IHp2. reflexivity.
simpl. rewrite -> IHp1. rewrite -> IHp2. reflexivity. Qed.

(* BEGIN FIX *)
(* ez a fuggveny az osszes valtozot 0-ra csereli *)
Fixpoint lezar (e : aexp) : aexp :=
(* END FIX *)
  match e with
  | ANum n => ANum n
  | AVar x => ANum 0
  | APlus a a' => APlus (lezar a) (lezar a')
  | AMult a a' => AMult(lezar a) (lezar a')
end.

(* BEGIN FIX *)
Lemma lezarZart (e : aexp) : zart (lezar e).
(* END FIX *)
induction e; simpl. apply szam. apply szam. apply osszeg. apply IHe1. apply IHe2. apply szorzat.
apply IHe1. apply IHe2. Qed.

(* BEGIN FIX *)
Lemma ugyanaz (e : aexp)(p : zart e) : lezar e = e.
(* END FIX *)
induction p. simpl. reflexivity. simpl. rewrite -> IHp1. rewrite -> IHp2. reflexivity.
simpl. rewrite -> IHp1. rewrite -> IHp2. reflexivity. Qed.

(* BEGIN FIX *)
Lemma szemantikaUgyanaz (e : aexp)(s : state) :
  aeval (lezar e) s = aeval e (fun _ => 0).
(* END FIX *)
induction e; simpl; try (reflexivity); rewrite -> IHe1; rewrite IHe2; reflexivity. Qed.
