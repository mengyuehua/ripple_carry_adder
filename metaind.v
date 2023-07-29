(*
  New induction schemes:

 1. two step natural number induction principle:

 Theorem nat_ind2 : forall (P : nat -> Prop),
  (P 0) -> (P 1) -> (forall (n:nat), (P n) -> (P (S (S n)))) ->
  (forall n, (P n)).

  Usage example:

  Lemma div2_rem2_ok : forall n, (div2 n) * 2 + (rem2 n) = n.
  Proof. induction n using nat_ind2. ...

  Note that this example can also be proved using Functional Scheme, see
  coq Reference Manual 8.0, Section 10.4

 2. two step list induction principle:

  Theorem listInd2 : 
    (P nil) -> (forall a, P (a::nil)) ->
    (forall l b c, (P l) -> (P (b::c::l))) -> 
    (forall l, (P l)).

 3. two equal length lists induction scheme:

  Theorem eqListInd : 
   P nil nil -> 
   (forall a b la lb, P la lb -> P (a::la) (b::lb))
   -> (forall la lb, len_eq la lb -> P la lb).

 4. two step induction over two equal length lists (2+3):

  Theorem eqListInd2 : 
   P nil nil -> (forall a b, P (a::nil) (b::nil)) ->
   (forall (a1 a2 b1 b2 : A) la lb, P la lb ->
     P (a1::a2::la) (b1::b2::lb))
   -> (forall la lb, len_eq A la lb -> P la lb).

  Usage example:  

  Lemma evens_mg : forall (l1 l2 : list A),
    length l1 = length l2 ->
     evens (mg_odd_even l1 l2) = l2.
  Proof.
   apply (eqListInd2 A (fun l1 l2 => evens (mg_odd_even l1 l2) = l2)).

 5. first list has one more element than the second :

  Theorem SeqListInd : 
   (forall a, P (a::nil) nil) -> 
   (forall a b la lb, P la lb -> P (a::la) (b::lb))
   -> (forall la lb, len_Seq la lb -> P la lb).

 6. reversed induction scheme revInd:
  Theorem revInd : forall P, P nil -> 
   (forall a l, P l -> P (l:+a)) -> (forall l, P l).
  Reference: rev_ind.

 7. change P l to P (rev l):
  Lemma revPP : forall P, (forall l, P (rev l)) -> (forall l, P l).

 8. two step reversed induction revInd2:
 Theorem revInd2 : forall P, P nil -> (forall a, P (a::nil)) ->
   (forall a b l, P l -> P ((l:+a):+b)) -> (forall l, P l).

 9. notTrueImply : forall P : Prop,  ~ True -> P.

 10. general double list induction:
  Theorem doubleListInd.

 11. non structural list induciton:
  Theorem non_struct_list_ind_ind : 
    (forall l, P 0 l) -> (forall n, P n nil) ->
    (forall n l, P n (f l) -> P (S n) l) -> 
    (forall n l, P n l).

 12. nat induction on general decreasing argument.
  Theorem natGenInd : 
    (forall n, 0<n -> f n < n) -> 
    P 0 -> 
    (forall n,  0<n -> P (f n) -> P n) ->
    (forall (n : nat), P n).

 13. list induction on decreasing list length.
  Theorem listLessInd : 
  (forall l, l<>nil -> length (f l) < length l) ->
    P nil -> 
    (forall l, P (f l) -> P l) ->
    (forall l, P l).

 14. generalization of listLessInd.
  Theorem listLessIndn : 
    forall n,
      (forall l, length (f l) < length l) ->
      (forall l, length l <= n -> P l) -> 
      (forall l, n <= length l -> P (f l) -> P l) ->
      (forall l, P l).

 15. 
  Theorem listLeInd : 
    forall n,
    (forall l, n <= length l -> length (f l) < length l) -> 
    (forall l, length l <= n -> P l) -> 
    (forall l, n <= length l -> P (f l) -> P l) ->
    (forall l, P l).

*)

Require Import List.
(* obselete
Require Import Le.
Require Import Lt.
*)
Require Export simple.
Require Import Lia.
(*
Require Import Arith.
*)
Require Import v816. 
(* 2023 redefine obselete names by new ones. *)
Import Nat.

(** A /\ .. nil<>nil /\ .. -> P *)
Ltac notNilImply :=
  let H := fresh "H" in
    intro H; decompose [and] H;
      match goal with
	[ h : nil <> nil |- _ ] => 
	   apply False_ind; apply h; auto
	| _ => idtac
      end.

(** False proposition -> any proposition. *)
Section FalseImply.

Variable A : Type.
Variable P : Prop.

Lemma notTrueImply :  ~ True -> P.
Proof. falseImply. Qed.
  
Lemma nilImply : nil(A:=A) <> nil(A:=A) -> P.
Proof. falseImply. Qed.

End FalseImply.

Section Convertion.

Variable P : nat -> Prop.

(** convert 0<n -> P n to P(S n) *)
Lemma lg0_imply : 
  (forall (n:nat), P(S n)) -> (forall (n:nat), 0<n -> P n).
Proof.
  intros H n.
  case n.
  intro.
  absurd (0 < 0).
  apply lt_irrefl.
  assumption.
  intros.
  apply H.
Qed.

End Convertion.

Section DepList.

Variable A : Type.
Variable P : list A->list A->Prop.
Implicit Types la lb : list A.
Implicit Types a b : A.
Arguments len_Seq [A].
Arguments len_eq [A].
(*
Implicit Arguments len_Seq [A].
Implicit Arguments len_eq [A].
*)

Definition doubleListRect 
  (f : P nil nil)
  (fa : (forall la, P la nil))
  (fb : (forall lb, P nil lb))
  (fab: (forall a b la lb, P la lb -> P (a::la) (b::lb))) :=
  fix F (l1 l2 : list A) {struct l1} : P l1 l2 :=
    match l1 as l0 return (P l0 l2) with
      | nil => 
	(match l2 as l0' return (P nil l0') with
	   nil => f
	   | b :: l0' => fb (b::l0')
	 end)
      | a :: la => 
	(match l2 as l0' return (P (a::la) l0') with
	   nil => fa (a::la)
	   | b :: lb => 
	     fab a b la lb (F la lb)
	 end)
    end.

(** one step double induction. *)
Theorem doubleListInd : 
   P nil nil -> 
   (forall la, P la nil) ->
   (forall lb, P nil lb) ->
   (forall a b la lb, P la lb -> P (a::la) (b::lb))
   -> (forall la lb, P la lb).
Proof. exact doubleListRect. Qed.

(** induction scheme for two list with length of left is one more than that of right. *)
Theorem SeqListInd : 
   (forall a, P (a::nil) nil) -> 
   (forall a b la lb, P la lb -> P (a::la) (b::lb))
   -> (forall la lb, len_Seq la lb -> P la lb).
Proof.
  intros P0 Pn.
  induction la.
  intros.
  unfold len_Seq in H.
  simpl in H.
  discriminate.  (* la = nil solved as an impossible case. *)

  induction lb.  (* induction within the base case of la *)
  unfold len_Seq in |- *.
  intro.
  simpl length at 2 in H. (* H: length (a::la)=length nil => la=nil *)
  assert (la = nil).
  apply (length_S_nil A a); assumption.
  rewrite H0; apply P0. (* base case of la solved *)

  (* solving the induction case of la *)
  unfold len_Seq in |- *; simpl in |- *.
  intro.
  assert (length la = S (length lb)).
  apply eq_add_S.
  assumption. (* length la = S (length lb) proved *)

  apply Pn. 
  apply IHla. (* forall lb, len_Seq la lb -> P la lb *)
  unfold len_Seq in |- *.
  assumption.

Qed.

(** two equal length lists induction scheme. *)
Theorem eqListInd : 
   P nil nil -> 
   (forall a b la lb, P la lb -> P (a::la) (b::lb))
   -> (forall la lb, len_eq la lb -> P la lb).
Proof.
  intros P0 Pn.
  induction la.
  intros.
  induction lb.  (* induction within the base case of la *)
  assumption.    (* base case of lb solved *)
  unfold len_eq in H; simpl in H.
  discriminate H. (* base case of la solved *)
  induction lb.  (* induction for induction case. *)
  intro H;  discriminate H.
  intro.
  apply Pn.
  apply IHla.
  unfold len_eq in *.
  simpl in H.
  apply eq_add_S; assumption. (* S m = S n => m = n *)
Qed.
End DepList.
Section NatIndExt.
(*
Implicit Arguments len_eq [A].
*)
Arguments len_eq [A].
(*
simple.even_succ
     : forall n : nat, 2 * S n = S (S (2 * n))
*)
(** derived nat induction scheme. *)
Theorem nat_ind2 : forall (P : nat->Prop),
  (P 0) -> (P 1) -> (forall (n:nat), (P n) -> (P (S (S n)))) ->
  (forall n, (P n)).
Proof.
intros.
elim (nat_split n). (* split n to even and odd. *)
intros.
elim H2. (* case analysis on H2 : n = 2 * x \/ n = 2 * x + 1 *)
 intro.
   rewrite H3.   (* make substitution H3 : n = 2 * x to get P(2*x) *)
   clear H3.     (* remove H3 : n = 2 * x *)
   clear H2.     (* remove H2 : n = 2 * x \/ n = 2 * x + 1. *)
   induction x.  (* so that induction on P(2*x) will not use the above 2 hypothesis. *)
+  simpl in |- *; assumption. (* solve P(2*0) *)
+  rewrite simple.even_succ.         (* P (2 * S x) =>   P (S (S (2 * x))) *)
    apply H1.    (* apply the main ind hypothesis: (P n) -> (P (S (S n) *)
    assumption.  (* subgoal n=2*x solved. *)
+ intro.          (* begin subgoal n=2*n+1. *)
   rewrite H3.
   clear H2 H3.
   induction x.
  simpl in |- *; assumption.
  rewrite simple.even_succ.
    rewrite succ_add1.
    apply H1.
    rewrite <- succ_add1.
    assumption.
Qed.


End NatIndExt.

Require Import List.

Section ListIndExt.

Variable A : Type.
Variable P : list A->Prop.
Implicit Type l : list A.
Implicit Type n : nat.
Implicit Type a b c : A.

(** convert list induction proof to nat induction proof. *)
Lemma natlist : 
  (forall n l,(length l = n -> (P l))) -> (forall l, (P l)).
Proof.
  intros H l.
  apply (H (length l)).
  trivial.
Qed.

(** an nat induction proof for list, proof P nil by n=0. *)
Ltac nat_list_ind l n tac :=
  intros; apply natlist; induction n using tac; 
  let h := fresh "H" in
  intros; assert(h: l=nil); [apply length_nil; assumption |
  rewrite h; assumption].  

(** a proof of the list induction scheme. *)
Lemma listind : 
  (P nil) -> (forall a l, P l  -> P (a::l)) -> (forall l, P l).
Proof.
  intros H H0.
  apply natlist.
  induction n.  (* convert list induction to nat induction. *)
  intros.
  assert (l = nil).
  apply length_nil; assumption.
  rewrite H2 in |- *; assumption.
  intro.
  case l.
  intro;  discriminate.
  intros a l1.
  simpl length in |- *.
  intro.
  apply H0.
  apply IHn.
  apply eq_add_S; assumption.
Qed.
(*
Implicit Arguments length_S [A].
Implicit Arguments length_S_nil [A].
*)
Arguments length_S [A].
Arguments length_S_nil [A].

(** proof of list induction. *)
Theorem listInd2 : 
  (P nil) -> (forall a, P (a::nil)) ->
  (forall l b c, (P l) -> (P (b::c::l))) -> 
  (forall l, (P l)).
Proof.
  intros.
  apply natlist.
  apply (nat_ind2 (fun n => forall l0, length l0 = n -> P l0)). 
(*  induction n using nat_ind2.*)
  intros.
  assert (l0 = nil).
  apply length_nil; assumption.
  rewrite H3 in |- *; assumption.
  intros.
  assert (exists a : _, exists tl : _, l0 = a :: tl).
  apply (length_S l0 0).
  assumption.
  destruct H3.
  destruct H3.
  rewrite H3 in |- *.
  rewrite H3 in H2.
  assert (x0 = nil).
  apply (length_S_nil x x0).
  assumption.
  rewrite H4 in |- *.
  apply H0.  (** proved base cases 0 and 1. *)
  intros.
  generalize H3.
  clear H3.
  case l0.   (* P l0, start case analysis until *)
  intro; 
  assumption.
  intros a l1.
  case l1.
  intros; apply H0. 
(* forall a0 l2, length (a :: a0 :: l2) = S (S n) -> P (a :: a0 :: l2) *)
  intros a0 l2.
  simpl in |- *.
  intro. 
  apply H1.
  apply H2.
  assert (S (length l2) = S n).
  apply eq_add_S; assumption.
  apply eq_add_S; assumption.
Qed.

(** equivalent to list_rect. *)
Definition list_rect1 (f : P nil) 
  (f0 : forall (a:A) (l : list A), P l -> P (a :: l)) :=
  fix F (l : list A) : P l :=
   match l as l0 return (P l0) with
     | nil => f
     | a :: l0 => f0 a l0 (F l0)
   end.

(** equivalent to list_ind. *)
Definition list_ind1 := list_rect1.

(** direct proof of list_ind. *)
Lemma listind_exact_proof : 
  (P nil) -> (forall a l, P l  -> P (a::l)) -> (forall l, P l).
Proof. exact list_ind1. Qed.

Definition list_rect2 (f : P nil) (g : forall a, P (a::nil))
  (f0 : forall a b l, P l -> P (a ::b:: l)) :=
  fix F (l : list A) : P l :=
   match l as l0 return (P l0) with
     | nil => f
     | a :: nil => g a 
     | a :: b :: l0 => f0 a b l0 (F l0)
   end.

(** equivalent to list_ind. *)
Definition list_ind2 := list_rect2.

Lemma listInd2_proof2 : 
  (P nil) -> (forall a, P (a::nil)) ->
  (forall b c l, (P l) -> (P (b::c::l))) -> 
  (forall l, (P l)).
Proof. exact list_rect2. Qed.

End ListIndExt.


Section RevList.
Notation "x :+ y" := (x ++ y :: nil) (at level 30, right associativity)  : list_scope.
Variable A : Type.
Implicit Types l : list A.
Implicit Types a b : A.
Implicit Types P : list A -> Prop.

Lemma revP : forall P, (forall l, P l) -> (forall l, P (rev l)).
Proof. intros; apply H. Qed.

Lemma revPP : forall P, (forall l, P (rev l)) -> (forall l, P l).
Proof. intros; rewrite <- rev_involutive in |- *; apply H. Qed.

(** induction scheme: P(l) => P(l:+a) *)
Theorem revInd : forall P, P nil -> 
   (forall a l, P l -> P (l:+a)) -> (forall l, P l).
Proof.
  intros.
  apply revPP.
  induction l0.
  auto.
  simpl in |- *.
  apply H0.
  assumption.
Qed.

(** two steps reversed induction. *)
Theorem revInd2 : forall P, P nil -> (forall a, P (a::nil)) ->
   (forall a b l, P l -> P ((l:+a):+b)) -> (forall l, P l).
Proof.
  intros; apply revPP.
  induction l0 using listInd2.
  auto.                    (* 1st subgoal solved *)
  simpl in |- *; apply H0. (* 2nd subgoal solved *)
  simpl in |- *; apply H1.
  assumption.              (* 3rd subgoal solved *)
Qed.

End RevList.

Section EqList2.
Variable A : Type.
Variable P : list A->list A->Prop.
Implicit Types la lb : list A.
Implicit Types a b : A.

(** two step induction over two equal length lists. *)
Theorem eqListInd2 : 
   P nil nil -> (forall a b, P (a::nil) (b::nil)) ->
   (forall (a1 a2 b1 b2 : A) la lb, P la lb ->
     P (a1::a2::la) (b1::b2::lb))
   -> (forall la lb, len_eq A la lb -> P la lb).
Proof.
  intros P0 P1 Pn.
  induction la using listInd2.
  induction lb.
  intro; assumption.
  intro.
  discriminate H.
  induction lb.
  intro;  discriminate.
  case lb.
  intro.
  apply P1.
  intros;  discriminate.
  induction lb using listInd2.
  intro;  discriminate.
  intro;  discriminate.
  intro.
  apply Pn.
  apply IHla.
  unfold len_eq in *.
  apply eq_add_S.
  apply eq_add_S.
  simpl in H.
  assumption.
Qed.

End EqList2.

Section NonStructualListInduction.

Variable A : Set.

Variable f : list A -> list A.

Variable P : nat -> list A -> Prop.

Implicit Types n : nat.
Implicit Types l : list A.


Definition non_struct_list_ind_rect 
  (g0 : (forall l, P 0 l))
  (gn : (forall n, P n nil))
  (gs : (forall n l, P n (f l) -> P (S n) l)) 
  :=
  fix F n l {struct n} : P n l :=
    match n as n0 return P n0 l with
      | 0 => g0 l
      | S n' =>
	(match l as l0 return P (S n') l0 with
	   nil => gn (S n')
	   | a::l' => gs n' (a::l') (F n' (f (a::l')))
	 end)
    end.

Theorem non_struct_list_ind : 
  (forall l, P 0 l) -> (forall n, P n nil) ->
  (forall n l, P n (f l) -> P (S n) l) -> 
  (forall n l, P n l).
Proof. exact non_struct_list_ind_rect. Qed.

End NonStructualListInduction.


Section NonStructualListInduction2.

Variable A : Set.

Variable dot : A -> A -> A.

Variable f : A -> list A -> list A.

Variable P : nat -> list A -> Prop.

Implicit Types n : nat.
Implicit Types l : list A.
Implicit Types a b : A.

(* non structural two step list induction. *)
Definition non_struct_list2_rect 
  (g0 : (forall l, P 0 l))
  (gn : (forall n, (P n nil)))
  (g1 : (forall n a, P n (a::nil)))
  (gs : (forall n b c l, 
          P n (f (dot b c) (b::c::l)) -> P (S n) (b::c::l)))
  :=
  fix F n l {struct n} : P n l :=
    match n as n0 return P n0 l with
      | 0 => g0 l
      | S n' =>
	(match l as l0 return P (S n') l0 with
	   nil => gn (S n')
	   | a :: nil => g1 (S n') a
	   | b::c::l' => 
	     gs n' b c l'
	       (F n' (f (dot b c) (b::c::l')))
	 end)
    end.

Lemma non_struct_list2_ind : 
  (forall l, P 0 l) -> 
  (forall n, P n nil) ->
  (forall n a, P n (a::nil)) ->
  (forall n b c l, 
          P n (f (dot b c) (b::c::l)) -> P (S n) (b::c::l)) ->
  (forall n l, P n l).
Proof. exact non_struct_list2_rect. Qed.

End NonStructualListInduction2.



(** generalized nat induction. *)
Section GenNatInd.

Variable f : nat -> nat.
Variable P : nat -> Prop.

Lemma natGenInd_aux : 
  (forall n, 0<n -> f n < n) -> 
  P 0 -> 
  (forall n,  0<n -> P (f n) -> P n) ->
  (forall (m n : nat) (g : n<=m), P n).
Proof.
  intros g0 g1 g2.
  induction m.
  intros.
  assert (0 = n).
  symmetry.
  apply le_n_O_eq; assumption. 
  rewrite <- H in |- *; assumption.
  intro n.
  case n.
  intro; assumption.
  intros.
  assert (n0 <= m).
  apply le_S_n.
  assumption.
  apply g2.
  apply lt_O_Sn.
  apply IHm.

(* goal:  f (S n0) <= m *)
  apply lt_n_Sm_le.            (*  f (S n0) <= S m *)
  apply (lt_le_trans (f (S n0)) (S n0) (S m)).
  apply g0.
  apply lt_O_Sn.
  f_equal; assumption.
Qed.

Theorem natGenInd : 
  (forall n, 0<n -> f n < n) -> 
  P 0 -> 
  (forall n,  0<n -> P (f n) -> P n) ->
  (forall (n : nat), P n).
Proof.
  intros.
  apply (natGenInd_aux H H0 H1 n n (le_refl n)); try assumption.
Qed.

End GenNatInd.

Section ListLessInd.

Variable A : Set.
Variable f : list A -> list A.
Variable P : list A -> Prop.

Implicit Types l : list A.

Lemma le_O : forall (n:nat), n<=0 -> n=0.
Proof. auto with arith. Qed.
(*
Implicit Arguments length [A].
*)
Arguments length [A].

Lemma length_le_O : forall l, length l <= 0 -> l = nil.
Proof. intros; apply length_nil; apply le_O; assumption. Qed.

Lemma listLessInd_aux : 
  (forall l, l<>nil -> length (f l) < length l) ->
  P nil -> 
  (forall l, P (f l) -> P l) ->
  (forall (m : nat) l (g: (length l)<=m), P l).
Proof.
  intros H0 H1 H2.
  induction m.
  intros.
  assert (l = nil); [ apply length_le_O; assumption | idtac ].
  rewrite H in |- *; assumption. (* P nil *)
  (* main goal :  forall l, length l <= S m -> P l *)
  intro.
  case l.
  intro; assumption.
  intros.
  apply H2.
  apply IHm.

  (*  length (f (a :: l0)) <= m *)
  apply lt_n_Sm_le.
  apply (lt_le_trans (length (f (a :: l0))) (length (a :: l0)) (S m)).
  apply H0.
  intro;discriminate. (* a :: l0 <> nil *)
  assumption.
Qed.

Theorem listLessInd : 
  (forall l, l<>nil -> length (f l) < length l) ->
  P nil -> 
  (forall l, P (f l) -> P l) ->
  (forall l, P l).
Proof. 
  intros H0 H1 H2 l.
  apply (listLessInd_aux H0 H1 H2 
     (length l) l (le_refl (length l))).
Qed.

(** generalization of listLess Ind. *)
Theorem listLessIndn : 
  forall n,
  (forall l, length (f l) < length l) ->
  (forall l, length l <= n -> P l) -> 
  (forall l, n <= length l -> P (f l) -> P l) ->
  (forall l, P l).
Proof.
induction n.
 intros.
   apply listLessInd.
  intros; apply H.
 apply H0.
   simpl in |- *; auto.
 intros; apply H1.
  lia.
 assumption.
intros.
  apply IHn.
 apply H.
intro.
  intro.
  apply H0.
  apply le_S; assumption.
intro.
  intro.
  assert (n < length l0 \/ n = length l0).
 apply le_lt_or_eq; assumption.
elim H3.
 intros.
   apply H1.
  apply lt_le_S; assumption.
 assumption.
intros.
  apply H0.
  rewrite <- H4 in |- *.
   lia.
Qed.

Lemma listLeInd_aux : 
  forall n,
  (forall l, n <= length l -> length (f l) < length l) -> 
  (forall l, length l <= n -> P l) -> 
  (forall l, n <= length l -> P (f l) -> P l) ->
  (forall (m : nat) l (g: (length l)<=m), P l).
Proof.
induction m.
 intros; apply H0.
   apply (le_trans (length l) 0 n).
  assumption.
  lia.
intros.
  assert (length l <= n \/ n < length l).
  lia.
elim H2.
 apply H0.
intro; apply H1.
 apply lt_le_weak; assumption.
apply IHm.
  apply lt_n_Sm_le.
  apply (lt_le_trans (length (f l)) (length l) (S m)).
 apply H.
   apply lt_le_weak; assumption.
assumption.
Qed.

Theorem listLeInd : 
  forall n,
  (forall l, n <= length l -> length (f l) < length l) -> 
  (forall l, length l <= n -> P l) -> 
  (forall l, n <= length l -> P (f l) -> P l) ->
  (forall l, P l).
Proof.
  intros n H0 H1 H2 l.
  apply (listLeInd_aux n H0 H1 H2 (length l) l (le_refl (length l))).
Qed.

End ListLessInd.

