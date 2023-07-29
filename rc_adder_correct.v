Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Wf.
Require Import Coq.micromega.Lia.
Infix "(+)" := xorb  (at level 38, left associativity)  : bool_scope.

(* implementation of ripple carry adder based on the type bool. *)
Section RippleCarryAdderBool.

Definition half_adder (a b : bool) : bool * bool := (* sum,carry *)
  pair (a (+) b) (a && b).

Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.
Theorem half_adder_ok' :  forall a b : bool,
  let (sum,carry) := half_adder a b in 
    (bool_to_nat sum) + (bool_to_nat carry) + (bool_to_nat carry)
  =  (bool_to_nat a) + (bool_to_nat b).
  destruct a, b; reflexivity.
Qed.

Coercion bool_to_nat : bool >-> nat.

(*半加器正确性证明*)
Theorem half_adder_ok :  forall a b : bool,
  let (sum,carry) := half_adder a b in 
    sum + carry + carry =  a + b.
Proof.
  unfold half_adder. destruct a, b; reflexivity.
Qed.

Definition full_adder (a b cin : bool) : bool * bool := (* sum,carry *)
  let (s1,c1) := half_adder a b in
  let (s2,c2) := half_adder s1 cin in
    pair s2 (c1 || c2).

(*全加器正确性证明*)
Theorem full_adder_ok :
 forall a b cin : bool,
   let (sum,cout) := full_adder a b cin in 
     a + b + cin = 2 * cout + sum.
Proof.
  unfold full_adder. destruct a,b,cin; reflexivity.
Qed.

Fixpoint rc_adder (xy : list (bool * bool)) (c : bool) {struct xy}
  : (list bool) * bool :=
  match xy with
    | (an,bn) :: xy' =>
      let (sn,cn) := full_adder an bn c in (**和链，进位链**)
	let (sum,carry) := rc_adder xy' cn in (**和，进位输出**)
	  ((sn::sum),carry)
    | nil => (nil,c)
  end.

Compute rc_adder [(true,false);(false,true);(true,true);(true,false)] true.


Fixpoint carry_out (xy : list (bool * bool)) (c_in : bool) : bool :=
  match xy with
  | [] => c_in
  | (x, y)::xy =>
      let (c_out, q) := full_adder x y c_in in
      carry_out xy c_out
  end.

Compute carry_out [(true,false);(false,true);(true,true);(true,false)] true.

(*Lemma rc_adder_correctness : forall (xy : list (bool * bool)) (c : bool),
  let sum_carry := rc_adder xy c in
  length (fst sum_carry) = length xy /\
  carry_out xy c = snd sum_carry.*)

Lemma rc_adder_correctness_left : forall (xy : list (bool * bool)) (c : bool),
  let sum_carry := rc_adder xy c in
  length (fst sum_carry) = length xy.
Proof.
  intros xy c sum_carry.
  induction xy as [| [x y] xy IHxy].
  simpl. reflexivity.
  simpl.
  unfold sum_carry. unfold rc_adder. unfold fst. unfold snd. simpl. 
  simpl in IHxy.
  destruct (full_adder x y c) as [s c'] eqn:H_adder.
    destruct (rc_adder xy c') as [sum carry] eqn:H_rc_adder.
  
  
