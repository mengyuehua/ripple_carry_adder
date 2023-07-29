(* Require Import coqadder.
Require Import require.
Require Import String.
Require Import Arith.
Require Import Lia.
Require Import List.
Import ListNotations.
Local Open Scope string_scope.



(* (* 整理到coqadder *)
Definition signallist_to_str (sc:(list Signal*Signal)) : string :=
  let (sum,cout) := sc in
   "("  ++ (signal2str cout) ++ ")".
Definition mk_net_list : (list Signal * Signal) -> string := signallist_to_str.
Compute mk_net_list (rc_adder_s [(Bitv "a",Bitv "b")] (Bitv "c")). *)




(* 另一个版本的行波进位加法器，保留下所有的进位信息 *)
Definition tpSum_allCarry_s := (list Signal * list Signal)%type.
Definition tpSum_allCarry_b := (list bool * list bool)%type.
Definition tpRcAdder_s_allc :=
  tpPairList_s -> Signal -> tpSum_allCarry_s.
Definition tpRcAdder_b_allc :=
  tpPairList_b -> bool -> tpSum_allCarry_b.

Fixpoint rc_adder_s_allc (ab:tpPairList_s) (c:Signal) : tpSum_allCarry_s :=
  let i := length ab in
  match i with
  | 0 => (nil, c :: nil)
  | S i' => match ab with
            | nil => (nil, c :: nil)
            | (an, bn) :: ab' =>
              let (sum, carry) := rc_adder_s_allc ab' c in
              let (sn, cn) := full_adder_s an bn (hd Bit0 carry ) in
                (sn :: sum, cn :: carry)
            end
  end.

Definition adder_s2b' (f:tpRcAdder_s_allc) : tpRcAdder_b_allc :=
  fun (ab:tpPairList_b) (c:bool) =>
    let sc := f (bpairs2spairs ab) (b2s c) in
    let sums := fst sc in
    let carry := snd sc in
       (slist2blist sums, slist2blist carry).

Definition rc_adder_b_allc : tpRcAdder_b_allc := adder_s2b' rc_adder_s_allc.

(* 对于1bit的加法，全加器和行波进位加法器的结果相同 *)
Lemma rcadder_eq_fulladder : forall a b cin : bool,
  hd false (fst (rc_adder_b_allc ((a,b)::nil) cin)) 
  = fst (full_adder_b a b cin) /\ 
  hd false (snd (rc_adder_b_allc ((a,b)::nil) cin)) 
  = snd (full_adder_b a b cin).
Proof.
  intros. destruct a,b,cin;split;reflexivity.
Qed.

(* boolean版本的正确性证明 *)
(* 进位的正确性 *)
Theorem rc_adder_allc_carry_red_b : 
  forall (a b:bool) (xy:tpPairList_b) (c:bool),
  hd false (snd (rc_adder_b_allc ((a,b)::xy) c)) =
  ci (a + b + (hd false (snd (rc_adder_b_allc xy c)))).
Proof.
intros. letPairSimp. destruct a,b,c0;letPairSimp;
try generalize (rc_adder_s_allc (bpairs2spairs xy) Bit1);
try generalize (rc_adder_s_allc (bpairs2spairs xy) Bit0);
intro;try destruct t;simpl;unfold s2b;simpl;
try destruct l1;simpl;try auto;
simpl;unfold s2b;try generalize (fun _ : string => true);
intro;destruct (signal2bool s b);auto.
Qed.

(* 求和的正确性 *)
Theorem rc_adder_allc_sum_red_b : 
  forall (a b:bool) (xy:tpPairList_b) (c:bool),
  (fst (rc_adder_b_allc ((a,b)::xy) c)) =
  si (a + b + (hd false (snd (rc_adder_b_allc xy c)))) 
  :: (fst (rc_adder_b_allc xy c)).
Proof.
intros. letPairSimp. destruct a,b,c0;letPairSimp;
try generalize (rc_adder_s_allc (bpairs2spairs xy) Bit1);
try generalize (rc_adder_s_allc (bpairs2spairs xy) Bit0);
intro; destruct t; simpl; unfold s2b; simpl;
destruct l1; simpl; auto;
simpl;unfold s2b;generalize (fun _ : string => true);
intro;destruct (signal2bool s b);auto.
Qed.

(* Signal版本的正确性证明 *)
(* 进位的正确性 *)
Lemma rc_adder_allc_carry_red_s : 
  forall (a b:Signal) (xy:tpPairList_s) (c:Signal),
  s2b (hd Bit0 (snd (rc_adder_s_allc ((a,b)::xy) c))) =
  ci ((s2b a) + (s2b b) + (s2b (hd Bit0 (snd (rc_adder_s_allc xy c))))).
Proof.
intros. letPairSimp.
generalize (rc_adder_s_allc xy c0). intro. 
destruct t. simpl. unfold s2b. simpl.
generalize (fun _ : string => true). 
intro. destruct l1; simpl; 
try destruct (signal2bool a b0);
try destruct (signal2bool b b0);
try destruct (signal2bool s b0); reflexivity.
Qed.

(* 求和的正确性 *)
Lemma rc_adder_allc_sum_red_s : 
  forall (a b:Signal) (xy:tpPairList_s) (c:Signal),
  map s2b (fst (rc_adder_s_allc ((a,b)::xy) c)) =
  (si ((s2b a) + (s2b b) + (s2b (hd Bit0 (snd (rc_adder_s_allc xy c)))))) 
  :: map s2b (fst (rc_adder_s_allc xy c)).
Proof.
intros. letPairSimp.
generalize (rc_adder_s_allc xy c0); intro;
destruct t; simpl;f_equal;unfold s2b;simpl;
generalize (fun _ : string => true); 
intro; destruct l1; simpl; 
try destruct (signal2bool a b0);
try destruct (signal2bool b b0);
try destruct (signal2bool s b0); reflexivity.
Qed.











 *)