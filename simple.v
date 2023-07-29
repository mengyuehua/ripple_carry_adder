(** 
  simple nat and list lemmas. 
  1) section SimpleLengthDef. define len_eq, len_Seq;
  2) section SimpleNat: even_succ,succ_add1,nat_split;
  3) section SimpleList. length_ni,length_S,length_SS.
  4) section LessThan.
*)
(* they are obselete and replaced by Nat
Require Import Le.
Require Import Lt.
*)
Require Import Arith. (* Nat.le_lt_trans *)
Import Nat.
Require Import List.
Require Import Lia.
Require Import ArithRing.

Ltac falseImply :=
  let P := fresh "P" in let H := fresh "H" in
    intros H; apply False_ind; apply H; auto.
(* example: nil<>nil -> *)

Section SimpleLengthDef.

Variable A : Type.
Implicit Types la lb : list A.

Definition len_eq la lb := length la = length lb.

Definition len_Seq la lb := length la = S (length lb).

Fixpoint even_listp (l : list A) : Prop :=
  match l with
    nil => True
    | a::b::l' => even_listp l'
    | _ => False
  end.

Definition rev_curry (f:A->A->A) : (A*A)->A :=
  fun (x:A*A) => f (fst x) (snd x).

(** [(a1,a2);..;(an,bn)] => [a1;a2;..;an;bn] *)
Definition flatten_pairlist (l:(list (A*A))) : list A :=
  fold_right (fun (x:A*A) (l':list A) => (fst x)::(snd x)::l') nil l.

End SimpleLengthDef.

Section SimpleNat.

Lemma one_neq_two : forall n, 0<n -> 1 <> 2 * n.
Proof. intro; lia. Qed.

Lemma even_succ : forall (n:nat),  2 * (S n) = S (S (2 * n)).
  intro; ring.
Qed.

Lemma succ_add1 : forall (n:nat), n+1 = S n.
  intro; ring.
Qed.

(** Natural number decomposition. *)
Lemma nat_split : forall (n:nat), exists k : nat,
  n = 2 * k \/ n = 2 * k + 1.
Proof.
intro; induction n.
 exists 0; left; reflexivity. (* base case. *)
 elim IHn. (* instanciate the "exists" hypothesis. *)
   intros. (* move the instanciated assumptions to hypothesis list. *)
   elim H. (* use the new \/ assumption to generate two subgoals. *)
  intro.   (* use left assumption of \/ *)
    exists x. (* prove the right of \/ of the goal with x. *)
    right; rewrite H0; ring. 
  intro; exists (x + 1). (* prove the right of \/ of the goal with x+1. *)
    left; rewrite H0; ring.
Qed.

End SimpleNat.






Section SimpleList.
Variable A : Type.
Implicit Type l : list A.
Implicit Type n : nat.

Lemma length_nil : forall l, length l = 0 -> l = nil.
Proof.  (* the proof does not use list induction. *)
  intro.
  case l.
  intro; trivial.
  intros.
  discriminate.
Qed.

Implicit Type tl : list A.

Lemma length_S : forall l n, 
  length l = S n -> exists a, (exists tl, l = a::tl).
Proof.
  intros l n.
  case l.
  intro;  discriminate. (* case l=nil proved. *)
  intros a l0 H.
  exists a; exists l0; trivial.
Qed.

Lemma length_SS : forall l n, 
  length l = S (S n) -> 
  exists a, (exists b, (exists tl, l = a::b::tl)).
Proof.
  intros l n.
  case l.
  intro;  discriminate.
  intros a l0.
  case l0.
  simpl in |- *; intro;  discriminate.
  intros; exists a; exists a0.
  exists l1; trivial.
Qed.

Lemma length_S_nil : forall x l, 
  length (x::l) = 1 -> l = nil.
Proof.
intros x l.
  simpl.
  case l.
  auto.
  intros.
  simpl in H.
  discriminate.
Qed.
End SimpleList.





Section EqList.

Variable A : Set.
Implicit Types l : list A.

Definition eq_hd (l1 l2 : list A) :=
  match l1, l2 with
    a1::_,a2::_ => a1 = a2
    |_,_ => False
  end.

Definition eq_2nd (l1 l2 : list A) :=
  eq_hd (tail l1) (tail l2).

Definition eq_tail2 (l1 l2 : list A) :=
  tail (tail l1) = tail (tail l2).

Lemma eq_hd_red : forall (l1 l2 : list A) (a b : A),
  eq_hd (a::l1) (b::l2) = (a=b).
Proof. intros; simpl; auto. Qed.

Theorem list_eq2 : forall (l1 l2 : list A),
  eq_hd l1 l2 -> tail l1 = tail l2 -> l1=l2.
Proof.
  unfold eq_hd in |- *; intros l1 l2; case l1; case l2; auto.
  intros a l; falseImply.
  intros a l; falseImply.
  intros; simpl in |- *.
  rewrite H in |- *.
  f_equal.
  simpl in H0; assumption.
Qed.

Lemma list_eq3 : forall (l1 l2 : list A),
  eq_hd l1 l2 -> eq_2nd l1 l2 -> eq_tail2 l1 l2 -> l1=l2.
Proof.
  unfold eq_2nd; intros; apply list_eq2; 
    [assumption| apply list_eq2; assumption].  
Qed.

End EqList.





Section LessThan.

Lemma absurd_le :  forall (m n:nat), n<=m -> m<n -> False.
Proof.
  intros.
  assert (n < n). 
  apply (le_lt_trans n m n); assumption.
  apply (lt_irrefl n); assumption.
Qed.

Lemma lt_le_trans_le : forall (m n q : nat),
  m < n -> n <= q -> m <= q.
Proof.
  intros; apply lt_le_incl.
  apply (lt_le_trans m n q); assumption.
Qed.

Lemma lt_gt : forall (m n : nat), n<m -> m>n.
Proof. auto. Qed.

End LessThan.
