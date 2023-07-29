Require Import List.
Require Import listext.
Import ListNotations.
Notation "x (+) y" := (xorb x y)(at level 50, left associativity).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Definition bool2 := (bool * bool)%type.
Definition sum_carry_b := (list bool * bool)%type.

Definition half_adder_b (a b : bool) : bool2 := 
 pair (a (+) b) (a && b).

Definition full_adder_b (a b cin : bool) : bool2 :=
  let (s1,c1) := half_adder_b a b in
  let (s2,c2) := half_adder_b s1 cin in
    pair s2 (c1 || c2).

Fixpoint rc_adder_b (ab:list (bool * bool)) (cin:bool) : sum_carry_b :=
  match ab with
    | (an,bn) :: ab' =>
      let (sum,carry) := rc_adder_b ab' cin in
    	let (sn,cn) := full_adder_b an bn carry in
	       ((sn::sum),cn)
    | nil => (nil,cin)
  end.


Compute half_adder_b true true.
Compute full_adder_b true true true.
Compute rc_adder_b [(true,false);(false,true)] true.


(* rc_adder *)
Fixpoint rem2 (n:nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S(S i) => rem2 i
  end.
Definition lg1 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => false
    | _ => true
  end.
Definition ci := lg1.  (* carry part of number n. *)
Definition si := rem2. (* sum part of number n.   *)

Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.
Coercion bool_to_nat : bool >-> nat.



(* ================================================================================== *)
(** ** Formal verification  *)

(* testbench of full_adder. *)
Definition ck_full_adder_truth_tbl full_adder_b : Prop :=
  forall a b cin : bool,
  full_adder_b a b cin =  
    match a,b,cin with
    | false,false,false  => (false, false)
    | false,false,true   => (true,  false)
    | false,true, false  => (true,  false)
    | false,true, true   => (false, true)
    | true, false,false  => (true,  false)
    | true, false,true   => (false, true)
    | true, true, false  => (false, true)
    | true, true, true   => (true,  true)
   end.

(* running exhaustive simulation -- formal verification. *)
Theorem full_adder_b_truth_tbl : 
 ck_full_adder_truth_tbl full_adder_b.
Proof.
  unfold ck_full_adder_truth_tbl.
  destruct a,b,cin; reflexivity.
Qed.

Definition ck_half_adder_truth_tbl half_adder_b : Prop :=
  forall a b : bool, half_adder_b a b =  
    match a,b with
    | false,false => (false, false)
    | false,true  => (true,  false)
    | true, false => (true,  false)
    | true, true  => (false, true)
   end.

(* running exhaustive simulation -- formal verification. *)
Theorem half_adder_b_truth_tbl : 
 ck_half_adder_truth_tbl half_adder_b.
Proof.
  unfold ck_half_adder_truth_tbl.
  destruct a,b; compute;reflexivity.
Qed.




(* behavior level formal verification. *)
Definition ck_full_adder_ok
 (full_adder : bool->bool->bool->(bool*bool)) : Prop :=
 forall a b cin : bool,
   let (sum,cout) := full_adder a b cin in 
     a + b + cin = 2 * cout + sum.

Theorem full_adder_b_high_level_verification : 
 ck_full_adder_ok full_adder_b.
Proof.
  unfold ck_full_adder_ok.
  destruct a, b, cin; reflexivity.
Qed.




(* 求和正确性 *)
Theorem rc_adder_sum_red_b :
  forall (a b:bool) (xy:list (bool * bool)) (c:bool),
  fst (rc_adder_b ((a,b)::xy) c) = 
  si (a + b + snd (rc_adder_b xy c)) :: (fst (rc_adder_b xy c)).
Proof.
intros. letPairSimp. destruct (rc_adder_b xy c).
simpl. destruct a,b,b0; auto.
Qed.

(* 进位正确性 *)
Theorem rc_adder_carry_red_b : 
  forall (a b:bool) (xy:list (bool * bool)) (c:bool),
  snd (rc_adder_b ((a,b)::xy) c) = 
  ci (a + b + (snd (rc_adder_b xy c))).
Proof.
intros. letPairSimp. destruct (rc_adder_b xy c).
simpl. destruct a,b,b0; auto.
Qed.














