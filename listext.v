(**
  Extended list library.

  Ltac: BasicList to simplify or normalize list exresssion.

  Ltacs:
  BasicList,letPairSimp,listInd, funRed.

  Sections:
  Even_listp,RevList,MapList,PairMap, Pair, FoldList,
  Last,Tail,ShiftRight.
*)

Require Import List.
Require Import tacdef.  (* listRec *)
Require Import simple.  (* even_listp *)
Require Import metaind. (* listInd2  *)
Require Import Lia.   (* to make rmLen work *)

Notation "x :+ y" := (x ++ y :: nil) (at level 30, right associativity)  : list_scope.

Fixpoint get_odd_elements {A:Type} (lst:list A) : list A :=
  match lst with
  | nil => nil
  | x :: nil => x :: nil
  | x :: _ :: xs => x :: get_odd_elements xs
  end.


Section Nil.

Variable A : Set.
Implicit Types l : list A.

Lemma cons_not_nil : forall l (a:A), a::l <> nil.
Proof. intros; intro; discriminate. Qed.

Arguments nil {A}.

Lemma nil_or_not : forall l, l=nil \/ ~ (l=nil).
Proof.
  intro; case l; auto.  (* case l=nil solved *)
  intros; right; apply cons_not_nil.
Qed.


Lemma list_3 : forall l (a:A), 1 < length l ->
  l = (hd a l)::(hd a (tail l))::(tail (tail l)).
Proof. intros l a; rmLen; auto. Qed.

End Nil.




Section Even_listp.

Variable A : Set.
Implicit Types l  : list A.

Arguments even_listp {A}.
Lemma even_listp_redr : forall (a b : A) l,
  even_listp ((l:+a):+b) = even_listp l.
Proof. induction l using listInd2; auto. Qed.

Lemma rev_even_listp : forall l,
  even_listp l -> even_listp (rev l).
Proof.
  induction l using listInd2; auto.
  simpl rev in |- *.
  simpl even_listp in |- *.
  rewrite even_listp_redr in |- *.
  assumption.
Qed.

Lemma not_even_listp_end : forall (a:A) l,
  even_listp l -> ~ (even_listp (l:+a)).
Proof. induction l using listInd2; auto. Qed.

Lemma even_listp_split : forall l, even_listp l \/ ~ even_listp l.
Proof.
  induction l using listInd2; auto.
  simpl in |- *; auto.
Qed.

Lemma even_listp_length : forall (l : list A),
  l <> nil -> even_listp l -> 1 < length l.
Proof.
  induction l using listInd2.
  falseImply.
  simpl in |- *.
  intro; falseImply.
  simpl in |- *; intros.
  autoLe.
Qed.

Arguments len_eq {A}.
Lemma length_even_listp : forall (l1 l2 : list A),
  len_eq l1 l2 -> even_listp l1 ->  even_listp l2.
Proof.
  apply (eqListInd2 A (fun l1 l2 => even_listp l1 -> even_listp l2)).
  auto.
  auto.
  intros.
  simpl in |- *.
  simpl in H0.
  apply H; assumption.
Qed.

End Even_listp.

Section HdTail.

Variable A : Set.
Variable a : A.

Implicit Types ll lr : list A.

Arguments cons_not_nil {A}.
Arguments even_listp {A}.

Lemma hd_tail_eq : forall ll lr, 
  ll<>nil -> lr<>nil ->
  hd a ll = hd a lr -> tail ll = tail lr -> ll = lr.
Proof.
  intros ll lr; case ll.
  falseImply.
  intros a0 l H.
  case lr.
  falseImply.
  intros a1 l0.
  simpl in |- *.
  intros.
  rewrite H1 in |- *; rewrite H2 in |- *; reflexivity.
Qed.

Lemma hd_tail_eq2 : forall ll lr, 
  1 < length ll -> 1 < length lr ->
  hd a ll = hd a lr -> 
  hd a (tail ll) = hd a (tail lr) ->
  tail (tail ll) = tail (tail lr) -> 
  ll = lr.
Proof.
  intros ll lr.
  rmLen.
  intros; apply hd_tail_eq.
  apply cons_not_nil.
  apply cons_not_nil.
  assumption.
  simpl in |- *.
  simpl in H1.
  simpl in H.
  simpl in H0.
  rewrite H0 in |- *; rewrite H1 in |- *; reflexivity.
Qed.

Lemma hd_tail_even_listp_eq : forall ll lr, 
  ll<>nil -> lr<>nil ->
  even_listp ll -> even_listp lr ->
  hd a ll = hd a lr -> 
  hd a (tail ll) = hd a (tail lr) ->
  tail (tail ll) = tail (tail lr) -> 
  ll = lr.
Proof.
  intros.
  apply hd_tail_eq2.
  apply even_listp_length; assumption.
  apply even_listp_length; assumption.
  assumption.
  assumption.
  assumption.
Qed.

End HdTail.

Section RevList.

Variable A  : Type.
Variable x y : A.
Variable l : list A.

Lemma rev_red :  rev (x::l) = rev l :+ x.
Proof. intros; simpl rev; trivial. Qed.

Lemma rev_redr : rev (l:+ x) = x::(rev l).
Proof. listRec l. Qed.

Lemma cons_l_cons : (x :: l) :+ y = x :: (l :+ y).
Proof. intros;  trivial. Qed.

Lemma app_l_cons : forall (l1 l2 : list A) (x:A),
  l1 ++ x :: l2 = l1 :+ x ++ l2.
Proof.
  induction l1.
  auto.
  intros.
  rewrite <- app_comm_cons in |- *.
  rewrite <- app_comm_cons in |- *.
  rewrite <- app_comm_cons in |- *.
  f_equal.
  apply IHl1.
Qed.

End RevList.

#[export] Hint Rewrite <- app_nil_end app_comm_cons : base_list.
#[export] Hint Rewrite cons_l_cons app_l_cons : base_list.
#[export] Hint Rewrite rev_involutive : base_list.

Ltac BasicList := autorewrite with base_list.

(** induction for f(l:+a) = g(a,f(l)). *)
Ltac redrInd l := 
  induction l as [| hd tl IH ]; 
  [auto | intros; rewrite cons_l_cons; simpl];
  rewrite IH; auto.

Section MapList.

 Variable A B : Type.
 Variable f : A -> B.
 Variable l : list A.
 Variable a : A.
 
 Lemma map_red : map f (a::l) = (f a) :: map f l.
 Proof. auto. Qed.

 Lemma map_redr : map f (l:+a) = (map f l):+(f a).
 Proof. listRec l. Qed. (* or redrInd l *)

End MapList.

Section PairMap.

Variable A B : Type.
Variable abl : list (A*A).
Variable ab  : A*A.

(** map fst/snd to list of pairs. *)
Definition mapfst := map (fst (A:=A) (B:=A)).
Definition mapsnd := map (snd (A:=A) (B:=A)).

Definition fstsplit abl := fst (split (A:=A) (B:=A) abl).
Definition sndsplit abl := snd (split (A:=A) (B:=A) abl).

(** split list A*A to (list A) * (list A)*)
Definition list_split := split (A:=A) (B:=A).
Definition list_comb  := combine (A:=A) (B:=A).

Lemma combine_red : forall (a:A) (b:B) (l1:list A) (l2:list B),
  combine (a::l1) (b::l2) = (a,b)::(combine l1 l2).
Proof. intros; simpl; trivial. Qed.

Lemma combine_nil : forall (l:list A),
  combine (A:=A) (B:=A) l nil = nil.
Proof. listRec l. Qed.

Lemma mapfst_red : 
  (mapfst (ab::abl)) = (fst ab)::(mapfst abl).
Proof. auto. Qed.

Lemma mapsnd_red : 
  (mapsnd (ab::abl)) = (snd ab)::(mapsnd abl).
Proof. auto. Qed.

Lemma mapfst_len : length (mapfst abl) = length abl.
Proof. listRec abl. Qed.

Lemma mapsnd_len : length (mapsnd abl) = length abl.
Proof. listRec abl. Qed.

Lemma split_fst_snd : 
  list_split abl = ((mapfst abl), (mapsnd abl)).
Proof. listRec abl. Qed.

End PairMap.

Section Fold_list.

 Variable A B : Type.
 Implicit Types l : list B.
 Implicit Types a : A.
 Implicit Types b : B.
 Variable f : A -> B -> A.  (* fold_left  f *)
 Variable g : B -> A -> A.  (* fold_right g *)

 Lemma fold_left_red : forall l a b,
   fold_left f (b::l) a = fold_left f l (f a b).
 Proof. auto. Qed.

 Lemma fold_right_red : forall l a b,
   fold_right g a (b::l) = g b (fold_right g a l).
 Proof. auto. Qed.

 Lemma fold_left_redr : forall l a b,
   fold_left f (l:+b) a = f (fold_left f l a) b .
 Proof. 
   induction l. auto. intros. simpl. apply (IHl (f a0 a)).
 Qed.

 Lemma fold_right_redr : forall l a b,
   fold_right g a (l:+b) = fold_right g (g b a) l.
 Proof.
   induction l. auto. intros; simpl.
   f_equal. apply (IHl a0 b).
 Qed.

End Fold_list.

Require Import ArithRing.

(** simplify let (a,b) := *)
Ltac letPairSimp :=
  intros; 
  toFstSnd;                      (* remove let (a,b):= c *)
  repeat(rewrite split_fst_snd); (* remove let (a,b):= list_split *)
  simpl.                         (* fst(a,b)=>a snd(a,b)=>b *)

(* start induction, solve base case, apply induction hypothesis. *)
Ltac listInd a :=
  try(introIH a); 
  letPairSimp;
  induction a as [| hd tl IH]; simpl; try(ring); auto; 
    simpl; 
      [(letPair; simpl in * |- *; rewrite IH) || (* e.g. sum_len *)
	(rewrite IH; letPair) || (* e.g. split_fst_snd *)
      letPairSimp];          
      simpl in * |- *; BasicArith.

(** prove induction property of form f(a::b) = g(a,f(b)). *)
Ltac funRed :=
  intros; simpl; letPairSimp; trivial.

Section Pair.

Variable A B : Type.
Variable a : A.
Variable b : B.

Lemma fst_red : fst (a,b) = a.
Proof. auto. Qed.

Lemma snd_red : snd (a,b) = b.
Proof. auto. Qed.

End Pair.

#[export] Hint Rewrite fst_red snd_red : base_red.

Section ListLength.

Variable A : Type.
Implicit Types a : A.
Implicit Types l : list A.

Lemma length_red : forall a l, length (a::l) = S(length l).
Proof. funRed. Qed.

Lemma length_redr : forall a l, length (l:+a) = S(length l).
Proof. listRec l. Qed.

End ListLength.

Section Last.

Variable A : Type.
Implicit Types a b c : A.
Implicit Types l : list A.

Lemma last_red1 : forall a c l, last (a::c::l) = last (c::l).
Proof. listRec l. Qed.

Lemma last_red2 : forall a c l, last (a::l:+c) = last (l:+c).
Proof. listRec l. Qed.

Lemma last_red : forall a b l, last (b::l) a = last l b.
Proof.
  intros; move l after a.
  generalize b;generalize a; clear a; clear b. (* keep abstraction over a b. *)
  induction l.
  auto.
  intros.                    (* IHl : forall a b, last (b :: l) a = last l b *)
  rewrite last_red1 in |- *. (*  last (a :: l) a0 = last (a :: l) b *)
  rewrite (IHl a0 a) in |- *.
  rewrite (IHl b a) in |- *.
  trivial.                    (* last l a = last l a *)
Qed.

Lemma removelast_red : forall a c l, 
  removelast (a::c::l) = a::(removelast (c::l)).
Proof. listRec l. Qed.

Lemma removelast_redl : forall a c l, 
  removelast (a::l:+c) = a::(removelast (l:+c)).
Proof. listRec l. Qed.

Lemma removelast_redr : forall c l, removelast (l:+c) = l.
Proof.
  induction l. auto.
  rewrite cons_l_cons in |- *.
  rewrite removelast_redl in |- *.
  rewrite IHl in |- *; trivial.
Qed.

Lemma removelast_len : forall l (a:A), 
  length (removelast (a::l)) = length l.
Proof.
  induction l.
  auto.
  intros; rewrite removelast_red in |- *.
  rewrite length_red in |- *.
  rewrite length_red in |- *.
  f_equal.
  apply IHl.
Qed.

End Last.

Section Tail.

Variable A : Set.
Implicit Types l  : list A.

Lemma tail_red : forall (a:A) l, tail (a::l) = l.
Proof. auto. Qed.

Lemma tail_redr : forall (a:A) l, 
  l<>nil -> tail (l:+a) = (tail l):+a.
Proof.
  listRec l.
  intro H; apply False_ind; apply H; trivial. (* nil<>nil -> *)
Qed.

Lemma tail_red2 : forall (a c : A) l,
  tail ((l:+a):+c) = (tail (l:+a)):+c.
Proof. listRec l. Qed.

Lemma tail_removelast : forall (l:list A),
  rev (tail (rev l)) = removelast l.
Proof.
  induction l.
  auto.
  simpl rev in |- *.
  induction l.        (* second induction. *)
  simpl in |- *.
  trivial.
  rewrite removelast_red in |- *.
  simpl rev in |- *.
  rewrite tail_red2 in |- *.
  rewrite rev_unit in |- *.
  f_equal.
  rewrite <- rev_red in |- *.
  assumption.
Qed.

End Tail.

Section ShiftRight.

Variable A : Type.
Implicit Types a b c : A.
Implicit Types l : list A.

(** list_shr a [a1;..;an] => (an, [a;a1;..;a(n-1)]) *)
Definition list_shr a l : A * (list A) :=
  (last l a, removelast (a::l)).

Lemma fst_list_shr_red : forall l a b,
  fst (list_shr a (b::l)) = fst (list_shr b l).
Proof.
  unfold list_shr in |- *.
  intros; rewrite fst_red; rewrite fst_red.
  apply last_red.
Qed.

Lemma snd_list_shr_red : forall a b l,
  snd (list_shr a (b::l)) = a::snd (list_shr b l).
Proof. listRec l. Qed.

(* first element of not empty list shift right reduction. *)
Lemma fst_nelist_shr_red : forall a b c l,
  fst (list_shr a (b::l:+c)) = fst (list_shr a (l:+c)).
Proof. listRec l. Qed.

(* second element of not empty list shift right reduction. *)
Lemma snd_nelist_shr_red : forall a b c l,
  snd (list_shr a (b::l:+c)) = a::snd (list_shr b (l:+c)).
Proof. listRec l. Qed.

Lemma fst_list_shr_redr : forall a b l,
  fst (list_shr a (l:+b)) = b.
Proof.
  induction l.
  auto.
  rewrite cons_l_cons in |- *.
  rewrite fst_nelist_shr_red in |- *.
  apply IHl.
Qed.

Lemma snd_list_shr_redr : forall a c l,
  snd (list_shr a (l:+c)) = a::l.
Proof.
  intros.
  unfold list_shr in |- *.
  rewrite <- cons_l_cons in |- *.
  rewrite removelast_redr in |- *.
  auto.
Qed.

Lemma list_shr_inv : forall a l,
  let w := list_shr a l in
    a::l = (snd w):+(fst w).
Proof.
  cbv zeta in |- *.
  intros.
  move l after a.
  generalize a; clear a.
  induction l.
  auto.
  intro.
  rewrite snd_list_shr_red in |- *.
  rewrite fst_list_shr_red in |- *.
  rewrite cons_l_cons in |- *.
  rewrite <- IHl in |- *.
  trivial.
Qed.

End ShiftRight.

#[export] Hint Rewrite cons_l_cons : base_redr.

(** f(a::l) => g(a,f(l)) *)
#[export] Hint Rewrite mapfst_red mapsnd_red  : base_red.
#[export] Hint Rewrite fold_left_red fold_right_red : base_red.
#[export] Hint Rewrite map_red rev_red : base_red.
#[export] Hint Rewrite length_red combine_red : base_red.

(** f(l:+a) => g(a,f(l)) *)
#[export] Hint Rewrite map_redr rev_redr : base_redr.

(* 2013.10.16 -- fold_right seems to be an error, replaced by fold_right_redr. *)
(* #[export] Hint Rewrite fold_left_redr fold_right : redr. *)
#[export] Hint Rewrite fold_left_redr fold_right_redr : redr.

(** f(rev(l)) => g(f(rev(l)). *)
#[export] Hint Rewrite map_rev : base_rev.