(* Require Import String. *)
Require Import Arith.
Require Import listext.
Require Import String.
Require Import Arith.
Require Import Lia.
Require Import List.
Require Import Ascii String.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================================= *)
(** ** Constructor and type conversion  *)
Inductive Signal : Set :=
  | Bit1  : Signal
  | Bit0  : Signal
  | Bitv  : string -> Signal
  | And2  : Signal -> Signal -> Signal
  | Or2   : Signal -> Signal -> Signal
  | Xor2  : Signal -> Signal -> Signal
  | Nand2 : Signal -> Signal -> Signal
  | Nor2  : Signal -> Signal -> Signal
  | Not1  : Signal -> Signal
  | Letb  : string -> Signal -> Signal -> Signal
with Signal_Pair : Set :=
  | Spair : Signal -> Signal -> Signal_Pair
  | Letb2 : string -> Signal -> Signal_Pair -> Signal_Pair.

Definition Signal2 := (Signal * Signal)%type.
Definition nandb a b := negb (andb a b).
Definition norb a b := negb (orb a b).
Definition b2n (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.
Coercion b2n : bool >-> nat.

Fixpoint signal2bool (s:Signal) (env : string -> bool) {struct s} : bool :=
 let s2b s := signal2bool s env in
 match s with
   | Bit0 => false
   | Bit1 => true
   | Not1 r => negb (s2b r)
   | And2  r1 r2 => andb  (s2b r1) (s2b r2)
   | Or2   r1 r2 => orb   (s2b r1) (s2b r2)
   | Xor2  r1 r2 => xorb  (s2b r1) (s2b r2)
   | Nand2 r1 r2 => nandb (s2b r1) (s2b r2)
   | Nor2  r1 r2 => negb (orb  (s2b r1) (s2b r2))
   | Bitv v => env v
   | Letb v e1 e2 => 
       let v1 := s2b e1 in
       let env1 x := if eqb x v then v1 else env x in
          signal2bool e2 env1
 end.

Definition signal2_to_bool (sc:Signal2) (env:string->bool) : bool*bool :=
  let (sum,cout) := sc in
    (signal2bool sum env, signal2bool cout env).
Definition s2b s := signal2bool s (fun x => true).
Definition b2s (b:bool) : Signal :=
  match b with
   | true  => Bit1
   | false => Bit0
  end.

(* convert boolean to diginal string "0" or "1". *)
Definition b2d (b:bool) : string :=
  match b with
   | true  => "1"
   | false => "0"
  end.





(* ================================================================================ *)
(** ** Develepment of adders  *)
Definition tpHalfAdder_s := Signal -> Signal -> Signal2.
Definition tpFullAdder_s := Signal -> Signal -> Signal -> Signal2.
Definition tpPairList_s := list (Signal * Signal).
Definition tpPairList_b := list (bool * bool).
Definition tpSumCarry_s := ((list Signal) * Signal)%type.
Definition tpSumCarry_b := ((list bool) * bool)%type.
Definition tpRcAdder_s := tpPairList_s -> Signal -> tpSumCarry_s.
Definition tpRcAdder_b := tpPairList_b -> bool -> tpSumCarry_b.
Definition tpList_s := list Signal.
Definition tpList_b := list bool.
Implicit Type ab : tpPairList_s.
Implicit Type c  : Signal.

Declare Scope Signal_scope.
Open Scope Signal_scope.
Infix "||"  := Or2   (at level 50, left associativity)  : Signal_scope.
Infix "&&"  := And2  (at level 40, left associativity)  : Signal_scope.
Infix "!&"  := Nand2 (at level 40, left associativity)  : Signal_scope.
Infix "(+)" := Xor2  (at level 38, left associativity)  : Signal_scope.
Infix "(-)" := Nor2  (at level 38, left associativity)  : Signal_scope.
Infix "!&" := nandb  (at level 40, left associativity)  : bool_scope.

Definition half_adder_s (a b : Signal) : Signal2 := 
 pair (a (+) b) (a && b).
Compute half_adder_s (Bitv "a") (Bitv "b").

Definition full_adder_s (a b cin : Signal) : Signal2 :=
  let (s1,c1) := half_adder_s a b in
  let (s2,c2) := half_adder_s s1 cin in
    pair s2 (c1 || c2).
Compute full_adder_s Bit0 Bit0 Bit1.

Fixpoint rc_adder_s (ab:tpPairList_s) (c:Signal) {struct ab} : tpSumCarry_s :=
  match ab with
    | (an,bn) :: ab' =>
      let (sum,carry) := rc_adder_s ab' c in
    	let (sn,cn) := full_adder_s an bn carry in
	       ((sn::sum),cn)
    | nil => (nil,c)
  end.

(* list (Signal*Signal) => list (bool*bool) *)
Definition spairs2bpairs (pl:tpPairList_s) : tpPairList_b :=
  List.map (fun (xy:Signal*Signal) => 
     (s2b (fst xy), s2b (snd xy))) pl.
(* list (bool*bool) => list (Signal*Signal) *)
Definition bpairs2spairs (pl:tpPairList_b) : tpPairList_s :=
  List.map (fun (xy:bool*bool) => 
    (b2s (fst xy), b2s (snd xy))) pl.
(* list Signal => list bool *)
Definition slist2blist (slist:tpList_s) : tpList_b :=
  List.map s2b slist.
(* list bool => list Signal *)
Definition blist2slist (blist:tpList_b) : tpList_s :=
  List.map b2s blist.
Compute blist2slist [true;false].
(* signal level adder => boolean level adder *)
Definition adder_s2b (f:tpRcAdder_s) : tpRcAdder_b :=
  fun (ab:tpPairList_b) (c:bool) =>
    let sc := f (bpairs2spairs ab) (b2s c) in
    let sums := fst sc in
    let carry := snd sc in
       (slist2blist sums, s2b carry).
(* bool层面的只定义了rc_adder, full_adder和half_adder没有定义 *)
Definition rc_adder_b : tpRcAdder_b := adder_s2b rc_adder_s.





(* ================================================================================= *)
(** ** simulation tools  *)
(* RTL-to-netlist *)
Fixpoint signal2str (s:Signal) {struct s} : string :=
 let s2s s := signal2str s in
 match s with
   | Bit0 => "0"
   | Bit1 => "1"
   | Not1 r => "~(" ++ (s2s r) ++ ")"
   | And2  r1 r2 => "("++(s2s r1) ++ "&" ++ (s2s r2)++")"
   | Or2   r1 r2 => "("++(s2s r1) ++ "|" ++ (s2s r2)++")"
   | Xor2  r1 r2 => "("++(s2s r1) ++ "^" ++ (s2s r2)++")"
   | Nand2 r1 r2 => "("++(s2s r1) ++ "~&" ++ (s2s r2)++")"
   | Nor2  r1 r2 => "(" ++((s2s r1) ++ "~|" ++ (s2s r2))++")"
   | Bitv v => v
   | Letb v e1 e2 => 
       let v1 := s2s e1 in
       let env1 x := if eqb x v then v1 else x in
          s2s e2 
 end.

Definition signal2_to_str (sc:Signal2) : string :=
  let (sum,cout) := sc in
   "(" ++ (signal2str sum) ++ "," 
   ++ (signal2str cout) ++ ")".

Definition mk_net1 : Signal -> string  := signal2str.
Definition mk_net2 : Signal2 -> string := signal2_to_str.
(* type of two inputs - two outputs function. *)
Definition tp_22 := Signal->Signal->Signal2.
(* type of two inputs and three outputs. *)
Definition tp_32 := Signal->Signal->Signal->Signal2.

Definition simulate_half_adder (f:tp_22) (a b: bool) : bool * bool :=
   let (x,y) := f (b2s a) (b2s b) in
      pair (s2b x) (s2b y).
Definition simulate_full_adder (f:tp_32) (a b c: bool) : bool * bool :=
   let (x,y) := f (b2s a) (b2s b) (b2s c) in
      pair (s2b x) (s2b y).

(* test *)
(* RTL-to-netlist synthesis *) 
Compute mk_net2 (half_adder_s (Bitv "a") (Bitv "b")).
Compute mk_net2 (full_adder_s (Bitv "a") (Bitv "b") (Bitv "c")).
(* Simulation *)
Compute (simulate_half_adder half_adder_s true false).       (* (true, false) *)
Compute (simulate_full_adder full_adder_s true false true).  (* (false, true) *)

(* 补充rc_adder的仿真 *)
Definition bpair2spair (a : (bool * bool)) : (Signal * Signal) :=
  let (x,y) := a in
  (b2s x,b2s y).
Fixpoint bplist2splist (a : tpPairList_b) : tpPairList_s :=
  match a with
  | [] => []
  | a1::al => bpair2spair a1 :: bplist2splist al
  end.
Definition sp2bp (a : (Signal * Signal)) : (bool * bool) :=
  let (x,y) := a in
  (s2b x,s2b y).
Fixpoint splist2bplist (a : tpPairList_s) : tpPairList_b :=
  match a with
  | [] => []
  | a1::al => sp2bp a1 :: splist2bplist al
  end.

Definition simulate (f:tpRcAdder_s) (ab:tpPairList_b) (c:bool) : tpSumCarry_b :=
  let (x,y) := f (bplist2splist ab) (b2s c) in
  (slist2blist x,s2b y).
(* 测试：1101+0110，初始进位为0 *)
Compute simulate rc_adder_s 
  [(true,false);(true,true);(false,true);(true,false)] false.
(* 测试结果：([false; false; true; true], true) *) 
(* 测试结果表示：sum=0011，carry=1 *)






(* ================================================================================== *)
(** ** Formal verification  *)
(* verification by testbench and formal verification by exhaustive simulation. *)

(* boolean level full adder type. *)
Definition full_adder_tp := bool -> bool -> bool -> bool * bool.
(* generate boolean valued full adder by simulator. *)
Definition full_adder_b : full_adder_tp :=
  simulate_full_adder full_adder_s.

(* testbench of full_adder. *)
Definition ck_full_adder_truth_tbl full_adder : Prop :=
  forall a b cin : bool,
  full_adder a b cin =  
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

(* behavior level formal verification. *)
Definition ck_full_adder_s_ok
 (full_adder : tpFullAdder_s) : Prop :=
 forall a b cin : bool,
   let '(a',b',cin') := (b2s a, b2s b, b2s cin)  in
   let (sum,cout)    := full_adder_s a' b' cin' in 
   let (sum,cout)    := (s2b sum, s2b cout) in
     a + b + cin = 2 * cout + sum.

Theorem full_adder_s_high_level_verification : 
 ck_full_adder_s_ok full_adder_s.
Proof.
  unfold ck_full_adder_s_ok.
  destruct a, b, cin; reflexivity.
Qed.




(* rc_adder *)
Fixpoint rem2 (n:nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S(S i) => rem2 i
  end.
Definition lg1 (n : nat) : bool :=
  match n with
    0 => false
    | 1 => false
    | _ => true
  end.
Definition ci := lg1.  (* carry part of number n. *)
Definition si := rem2. (* sum part of number n.   *)
Compute si 2. Compute ci 2.

(* boolean版本的正确性证明 *)
(* carry的正确性 *)
Theorem rc_adder_b_carry_red : 
  forall (a b:bool) (xy:tpPairList_b) (c:bool),
  snd (rc_adder_b ((a,b)::xy) c) = 
  ci (a + b + (snd (rc_adder_b xy c))).
Proof.
intros. letPairSimp.
generalize (rc_adder_s (bpairs2spairs xy) (b2s c)).
intro. destruct t. simpl. unfold s2b. simpl.
destruct a,b; trivial;simpl;
generalize (fun _ : string => true);
intro b; generalize (signal2bool s b); intro b0;
destruct b0; reflexivity.
Qed.

(* sum的正确性 *)
Theorem rc_adder_b_sum_red :
  forall (a b:bool) (xy:tpPairList_b) (c:bool),
  fst (rc_adder_b ((a,b)::xy) c) = 
  si (a + b + snd (rc_adder_b xy c)) :: (fst (rc_adder_b xy c)).
Proof.
intros. letPairSimp.
generalize (rc_adder_s (bpairs2spairs xy) (b2s c)).
intro. destruct t. simpl. unfold s2b. simpl.
destruct a,b;simpl;
generalize (fun _ : string => true); intro b;
destruct (signal2bool s b);reflexivity.
Qed.

(* Signal版本的正确性证明 *)
(* 进位的正确性 *)
Theorem rc_adder_s_carry_red : 
  forall (a b:Signal) (xy:tpPairList_s) (c:Signal),
  s2b (snd (rc_adder_s ((a,b)::xy) c)) = 
  ci ((s2b a) + (s2b b) + (s2b (snd (rc_adder_s xy c)))).
Proof.
intros. letPairSimp.
generalize (rc_adder_s xy c). intro. destruct t.
simpl. unfold s2b. simpl.
generalize (fun _ : string => true). intro.
destruct (signal2bool a b0);destruct (signal2bool b b0);
destruct (signal2bool s b0); reflexivity.
Qed.

(* 求和的正确性 *)
Theorem rc_adder_s_sum_red : 
  forall (a b:Signal) (xy:tpPairList_s) (c:Signal),
  map s2b (fst (rc_adder_s ((a,b)::xy) c)) =
  (si ((s2b a) + (s2b b) + (s2b (snd (rc_adder_s xy c))))) 
  :: map s2b (fst (rc_adder_s xy c)).
Proof.
intros. letPairSimp.
generalize (rc_adder_s xy c). intro. destruct t.
simpl. f_equal. unfold s2b. simpl. 
generalize (fun _ : string => true). intro.
destruct (signal2bool a b0);destruct (signal2bool b b0);
destruct (signal2bool s b0);reflexivity.
Qed.

(* 补充证明 *)
(* 2^n *)
Fixpoint sftl n : nat :=
  match n with
  | 0 => 1
  | S n => let m := sftl n in 2*m
  end.
Fixpoint blist2n (nlist:(list bool)) : nat :=
  match nlist with
  | nil => 0
  | hd :: tl => hd * (sftl (List.length tl)) + blist2n(tl)
  end.
Definition slist2n (p:list Signal) := blist2n (slist2blist p).
Definition s2n (s:Signal) : nat := b2n (s2b s).

(* bool版本 *)
Lemma b2s2b : forall c : bool, s2b (b2s c) = c.
Proof. destruct c; reflexivity. Qed.
Lemma split_simpl : forall (a b:bool) (xy:tpPairList_b),
  split ((a, b) :: xy) = (a::fst(split xy) , b::snd(split xy)).
Proof. intros. letPairSimp. destruct (split xy). auto. Qed.
Lemma blist2n_split : forall (a:bool) (b:list bool),
  let n := List.length b in
  blist2n (a::b) = (b2n a) * (sftl n) + (blist2n b).
Proof. intros. simpl. unfold n. auto. Qed.
Lemma rc_adder_b_split :forall (xy:tpPairList_b) (c:bool), 
       rc_adder_b xy c = (fst(rc_adder_b xy c), snd(rc_adder_b xy c)).
Proof. auto. Qed.
Lemma cons_len : forall (A:Type) (a:A) (b:list A),
  List.length (a::b) = List.length b + 1.
Proof. simpl. lia. Qed.
Lemma rc_adder_b_len : forall (xy:tpPairList_b) (c:bool),
  List.length (fst (rc_adder_b xy c)) = List.length xy.
Proof. intros. induction xy;induction c;auto;
destruct a as (a1,a2); rewrite cons_len;
rewrite <- IHxy; rewrite rc_adder_b_sum_red;
rewrite cons_len; auto. Qed.
Lemma sftl_simpl : forall n:nat, sftl (n+1) = sftl n + sftl n.
Proof. intro. induction n;auto. simpl.
do 2 rewrite <- plus_n_O. rewrite IHn. auto. Qed.

Theorem rc_adder_b_correct : 
  forall (xy:tpPairList_b) (c:bool),
    let (sum,carry) := rc_adder_b xy c in
    let (x,y) := list_split bool xy in
    let (n,m) := (blist2n x, blist2n y) in 
    let len   := List.length xy in
      n+m+c = (blist2n sum) + carry * (sftl len).
Proof.
intros. induction xy. 
simpl. rewrite b2s2b. lia.
rewrite rc_adder_b_split. rewrite split_fst_snd.
rewrite cons_len.
destruct a as (a,b). autorewrite with base_red.
(* 处理IHxy *)
rewrite rc_adder_b_split in IHxy. rewrite split_fst_snd in IHxy.
(* 调整等式左边以应用IHxy *)
do 2 rewrite blist2n_split. rewrite rc_adder_b_sum_red. 
rewrite rc_adder_b_carry_red. rewrite mapfst_len.
rewrite mapsnd_len. do 2 rewrite <- Nat.add_assoc. 
rewrite (Nat.add_comm (a*sftl (Datatypes.length xy)) (blist2n (mapfst bool xy) +
 (b*sftl (Datatypes.length xy) + blist2n (mapsnd bool xy) + c))).
rewrite <- (Nat.add_assoc (b * sftl (Datatypes.length xy)) (blist2n (mapsnd bool xy)) c).
rewrite (Nat.add_comm (b*sftl (Datatypes.length xy)) (blist2n (mapsnd bool xy) + c)).
do 2 rewrite Nat.add_assoc. rewrite IHxy.
(* 分类讨论 *)
rewrite blist2n_split. rewrite rc_adder_b_len.
destruct a,b,(snd (rc_adder_b xy c));simpl;
set (t:=Datatypes.length xy); try repeat rewrite <- plus_n_O;
try rewrite sftl_simpl;try auto.
symmetry. rewrite Nat.add_assoc.  
do 2 f_equal. rewrite Nat.add_comm. f_equal.
rewrite Nat.add_assoc. f_equal. rewrite Nat.add_assoc. f_equal.
rewrite Nat.add_comm.  f_equal. rewrite Nat.add_assoc. f_equal.
rewrite Nat.add_comm.  f_equal. rewrite Nat.add_comm. f_equal.
Qed.


(* Signal版本 *)
(* 一些辅助引理 *)
Lemma rc_adder_s_split : forall (xy:tpPairList_s) (c:Signal),
  rc_adder_s xy c = (fst (rc_adder_s xy c), snd (rc_adder_s xy c)).
Proof. intros. induction xy. auto.
simpl. destruct a. rewrite IHxy. auto. Qed.
Lemma rc_adder_s_len : forall (xy:tpPairList_s) (c:Signal),
  List.length (fst (rc_adder_s xy c)) = List.length xy.
Proof. intros. induction xy;simpl. auto. destruct a. 
rewrite rc_adder_s_split. simpl. rewrite IHxy. auto. Qed.
Lemma pair_len : forall a:tpPairList_b, 
  Datatypes.length (bpairs2spairs a) = Datatypes.length a.
Proof. intro. induction a. auto.
simpl. f_equal. rewrite IHa. auto. Qed.
Lemma si_red : forall a:bool, si a = a.
Proof. destruct a;auto. Qed.

Definition ck_rc_adder_s_ok (rc_adder : tpRcAdder_s) : Prop :=
  forall (xy : tpPairList_b) (c : bool),
    let (x,y)    := list_split bool xy in
    let (n,m)    := (blist2n x, blist2n y) in 
    let (xy',c') := (bpairs2spairs xy,b2s c) in
    let (sum',carry') := rc_adder_s xy' c' in
    let (sum,carry)   := (slist2blist sum', s2b carry') in
    let len := List.length xy in
      n+m+c = (blist2n sum) + carry * (sftl len).

Theorem rc_adder_s_correct : 
  ck_rc_adder_s_ok rc_adder_s.
Proof.
unfold ck_rc_adder_s_ok. intros. induction xy.
- simpl. rewrite b2s2b. lia.
- destruct a as (a1,a2). rewrite split_fst_snd.
autorewrite with base_red. do 2 rewrite blist2n_split.
rewrite Nat.add_assoc. rewrite mapfst_len. rewrite mapsnd_len.
rewrite rc_adder_s_split.
(* 处理IHxy *)
rewrite rc_adder_s_split in IHxy. rewrite split_fst_snd in IHxy.
(* 应用IHxy *)
rewrite (Nat.add_comm (a1 * sftl (Datatypes.length xy))(blist2n (mapfst bool xy))).
do 3 rewrite <- Nat.add_assoc. 
rewrite (Nat.add_comm (a2 * sftl (Datatypes.length xy))(blist2n (mapsnd bool xy)+c)).
rewrite (Nat.add_comm (a1 * sftl (Datatypes.length xy))(blist2n (mapsnd bool xy)+c+(a2 * sftl (Datatypes.length xy)))).
do 3 rewrite Nat.add_assoc. rewrite IHxy.
(* right *)
set(t:=Datatypes.length xy). unfold slist2blist.
assert(bpairs2spairs ((a1, a2) :: xy) = (b2s a1,b2s a2)::bpairs2spairs xy). simpl. auto.
rewrite H;clear H. rewrite rc_adder_s_sum_red. rewrite rc_adder_s_carry_red.
do 2 rewrite b2s2b.
(* 分类讨论 *)
destruct a1,a2,c;simpl;try repeat rewrite <- plus_n_O.
+ rewrite Nat.add_assoc. f_equal. f_equal. 
rewrite Nat.add_comm. f_equal. rewrite map_length. rewrite rc_adder_s_len. 
rewrite pair_len. f_equal. rewrite si_red. auto.
+ rewrite Nat.add_assoc. f_equal. f_equal. 
rewrite Nat.add_comm. f_equal. rewrite map_length. rewrite rc_adder_s_len. 
rewrite pair_len. f_equal. rewrite si_red. auto.
+ destruct (s2b (snd (rc_adder_s (bpairs2spairs xy) Bit1)));simpl.
do 3 rewrite Nat.add_assoc. do 2 rewrite <- plus_n_O. f_equal.
do 3 rewrite <- plus_n_O. rewrite Nat.add_comm. f_equal.
rewrite map_length. rewrite rc_adder_s_len. rewrite pair_len.
unfold t. auto.
+ destruct (s2b (snd (rc_adder_s (bpairs2spairs xy) Bit0)));simpl.
do 3 rewrite Nat.add_assoc. do 2 rewrite <- plus_n_O. f_equal.
do 3 rewrite <- plus_n_O. rewrite Nat.add_comm. f_equal.
rewrite map_length. rewrite rc_adder_s_len. rewrite pair_len.
unfold t. auto.
+ destruct (s2b (snd (rc_adder_s (bpairs2spairs xy) Bit1)));simpl.
do 3 rewrite Nat.add_assoc. do 2 rewrite <- plus_n_O. f_equal.
do 3 rewrite <- plus_n_O. rewrite Nat.add_comm. f_equal.
rewrite map_length. rewrite rc_adder_s_len. rewrite pair_len.
unfold t. auto.
+ destruct (s2b (snd (rc_adder_s (bpairs2spairs xy) Bit0)));simpl.
do 3 rewrite Nat.add_assoc. do 2 rewrite <- plus_n_O. f_equal.
do 3 rewrite <- plus_n_O. rewrite Nat.add_comm. f_equal.
rewrite map_length. rewrite rc_adder_s_len. rewrite pair_len.
unfold t. auto.
+ rewrite map_length. rewrite rc_adder_s_len. rewrite pair_len.
set(m:=blist2n (map s2b (fst (rc_adder_s (bpairs2spairs xy) Bit1)))).
set(n:=s2b (snd (rc_adder_s (bpairs2spairs xy) Bit1))).
fold t. rewrite <- Nat.add_assoc. rewrite Nat.add_comm.
rewrite (Nat.add_comm m (ci n * (sftl t + sftl t))).
rewrite Nat.add_assoc. f_equal. destruct n;simpl;easy.
+ rewrite map_length. rewrite rc_adder_s_len. rewrite pair_len.
set(m:=blist2n (map s2b (fst (rc_adder_s (bpairs2spairs xy) Bit0)))).
set(n:=s2b (snd (rc_adder_s (bpairs2spairs xy) Bit0))).
fold t. rewrite <- Nat.add_assoc. rewrite Nat.add_comm.
rewrite (Nat.add_comm m (ci n * (sftl t + sftl t))).
rewrite Nat.add_assoc. f_equal. destruct n;simpl;easy.
Qed.








(* ================================================================================= *)
(** ** generate verilog code *)
(* 这个模块目前还有问题，生成代码的时候只处理了Bitv的情况，后面还需要修改 *)
Fixpoint gv (s:Signal) : string :=
 match s with
   | Bit0        => "1'b0"
   | Bit1        => "1'b1"
   | Bitv v      => v
   | Not1 r      => "~(" ++ (gv r) ++ ")"
   | And2  r1 r2 => "(" ++ (gv r1) ++ ")&("  ++ (gv r2) ++ ")"
   | Or2   r1 r2 => "(" ++ (gv r1) ++ ")|("  ++ (gv r2) ++ ")"
   | Xor2  r1 r2 => "(" ++ (gv r1) ++ ")^("  ++ (gv r2) ++ ")"
   | Nand2 r1 r2 => "(" ++ (gv r1) ++ ")~&(" ++ (gv r2) ++ ")"
   | Nor2  r1 r2 => "(" ++ (gv r1) ++ ")~|(" ++ (gv r2) ++ ")"
   | Letb v r1 r2 => "
      assign " ++ v ++ " = " ++ (gv r1) ++ ";" ++ (gv r2) ++ ";"
 end.

Definition gv_half_adder (f:tpHalfAdder_s) (x y : Signal) : string :=
  let (sum,cout) := f x y in
  let x1 := gv x in
  let y1 := gv y in
" module half_adder(
             input   " ++ x1 ++ "," ++ y1 ++ ",
             output  sum,cout                  
         );                                    
                                               
             assign sum = " ++ (gv sum) ++ ";  
             assign cout = " ++ (gv cout) ++ ";
                                               
         endmodule  ".

Definition gv_full_adder (f:tpFullAdder_s) (x y z: Signal) : string :=
  let (sum,cout) := f x y z in
  let x1 := gv x in
  let y1 := gv y in
  let z1 := gv z in
" module full_adder(
             input   " ++ x1 ++ "," ++ y1 ++ "," ++ z1 ++ ",
             output  sum,cout                  
         );                                    
                                               
             assign sum = " ++ (gv sum) ++ ";  
             assign cout = " ++ (gv cout) ++ ";
                                               
         endmodule  ".

(* 1. gv_half_adder : Signal  -> Verilog
   2. gs_half_adder : Verilog -> Signal
   给一个加法器half_adder: 
   correct_verilog gs_half_adder (gv_half_adder half_adder) = half_adder  *)
(*
Compute gv_half_adder half_adder_s a b.
     = " module half_adder(
             input   a,b,
             output  sum,cout
         );
             assign sum = (a)^(b);
             assign cout = (a)&(b);
         endmodule  "
*)


(* 生成行波进位加法器的verilog代码 *)
(* sum : list Signal => list string *)
Definition divmod (x y : nat) : nat * nat := (x / y, x mod y).
Definition natToDigit (n : nat) : ascii :=
  match n with
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | 9 => "9"
    | _ => "0"
  end.
Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.
Definition writeNat (n : nat) : string :=
  writeNatAux n n "".
Definition mk_fresh (v:string) (cnt:nat) : string :=
   v ++ (writeNat cnt).

Definition Signallist2stringlist (Signal_list:tpList_s) : list string :=
  List.map gv Signal_list.
(* 提取输入中所有变量的名字 *)
Definition input_conv (ab:tpPairList_s) : string :=
  String.concat "," (List.map (fun '(a, b) => gv a ++ "," ++ gv b) ab).

Compute input_conv [(Bitv"a1",Bitv"b1");(Bitv"a2",Bitv"b2")].
(* "a1,b1,a2,b2" *)


Fixpoint sum_split (sum:list string) (n:nat) {struct n}: string :=
  let sum_rev := rev sum in
  match n with
  | 0 => ""
  | S m => (sum_split sum m) ++ 
           (mk_fresh "assign sum" (n-1)) ++ " = " ++ 
           (nth (n-1) sum_rev "unknown") ++ ";" ++ "
        " 
  end.
Definition c := Bitv "c".
Definition l := [(Bitv "a1", Bitv "b1"); (Bitv "a0", Bitv "b0")].
Compute sum_split (Signallist2stringlist (fst (rc_adder_s l c))) 2.
(* assign sum[0] = ((a2)^(b2))^(c);
   assign sum[1] = ((a1)^(b1))^(((a2)&(b2))|(((a2)^(b2))&(c))); *)

Definition gv_rc_adder (f:tpRcAdder_s) (ab:tpPairList_s) (c: Signal) : string :=
  let (sum, carry) := f ab c in  
  let n := Datatypes.length ab in
  let ab_list := input_conv ab in
  let c1 := gv c in              
  let sum_list := String.concat "," (List.map gv sum) in
" module rc_adder(                                
             input " ++ ab_list ++ "," ++ c1 ++ ",
             output " ++ (mk_fresh "sum" (n-1)) ++ "," ++ (mk_fresh " sum" 0) ++", cout
         );" ++ "
        "++ "
        " ++ (sum_split (Signallist2stringlist sum) n) ++
             "assign cout = " ++ (gv carry) ++ ";
                                                
         endmodule  ".

(* test *)
Definition a := Bitv "a".
Definition b := Bitv "b".
Definition l4 := [(Bitv "a1", Bitv "b1"); (Bitv "a2", Bitv "b2");
                  (Bitv "a3", Bitv "b3"); (Bitv "a4", Bitv "b4")].


(* Definition l := [(Bitv "a1", Bitv "b1"); (Bitv "a0", Bitv "b0")]. *)
Compute gv_rc_adder rc_adder_s l c.

Compute gv_half_adder half_adder_s a b.
(*
     = " module half_adder(
             input   a,b,
             output  sum,cout                  
         );                                    
                                               
             assign sum = (a)^(b);  
             assign cout = (a)&(b);
                                               
         endmodule  "
*)
Compute gv_full_adder full_adder_s a b c.
Compute gv_rc_adder rc_adder_s l4 c.









(* ================================================================================= *)
(** ** generate netlist *)
(* direct signal *)
Inductive tpImmed :=
  LowV | HighV | SigVar : string -> tpImmed.
Inductive tpGateNo :=
  | NotGate | AndGate | OrGate 
  | XorGate | NorGate | NandGate.

(* type of netlist is a 4 element tuple: v := (op v1 v2) *)
Definition tpGateAssign2 := 
  (string * (tpGateNo * tpImmed * tpImmed))%type.
Definition tpGateAssign1 := 
  (string * (tpGateNo * tpImmed))%type.
(* type of immediate assignment is a pair v := i. *)
Definition tpImmedAssign :=
  (string * tpImmed)%type.

(* type of single element assignment: v := x *)
Inductive tpNetEle :=
  | ImmedAss : tpImmedAssign -> tpNetEle
  | GateAss1 : tpGateAssign1 -> tpNetEle
  | GateAss2 : tpGateAssign2 -> tpNetEle.

Definition tpNetlist := list tpNetEle.


Local Open Scope list_scope.

(* an auxiliary function to generate netlist. *)
Fixpoint mkn (s:Signal) (cnt:nat) (nets:tpNetlist) : 
nat * tpNetlist * string :=
 let mkass2 r1 r2 gate_str gate_no :=
   let v1 := mk_fresh (gate_str++"L") cnt in
   let '(cnt2, nets2, v2) := mkn r1 (cnt+1) nets in
   let '(cnt3, nets3, v3) := mkn r2 (cnt2+1) nets2 in
   let ass := GateAss2 (v1,(gate_no, SigVar v2,SigVar v3)) in
     (cnt3+1, nets3++[ass],v1) 
 in
 match s with
   | Bit0   => (cnt, nets, "0")
   | Bit1   => (cnt, nets, "1")
   | Bitv v => (cnt, nets, v)
   | Not1 r =>
       let v1 := mk_fresh "N" cnt in
       let v2 := mk_fresh "N" (cnt+1) in
       let ass := GateAss1 (v1,(NotGate, SigVar v2)) in
          mkn r (cnt+2) (ass::nets)
   | And2  r1 r2 => mkass2 r1 r2 "And2"  AndGate
   | Or2   r1 r2 => mkass2 r1 r2 "Or2"   OrGate
   | Xor2  r1 r2 => mkass2 r1 r2 "Xor2"  XorGate
   | Nand2 r1 r2 => mkass2 r1 r2 "Nand2" NandGate
   | Nor2  r1 r2 => mkass2 r1 r2 "Nor2"  NorGate
   | Letb v r1 r2 => 
       let '(cnt1, nets1, v1) := (mkn r1 cnt nets) in
          mkn r2 cnt1 nets1
 end.

Definition mk_netlist (s:Signal) : tpNetlist :=
  let '(_,nets,_) := (mkn s 0 []) in nets.

Definition mk_netlist2 (sc : Signal2) : list tpNetlist :=
  let (sum,cout) := sc in
     (mk_netlist sum) :: (mk_netlist cout) :: nil.

(* test *)
(* half_adder : (x^y,x&y) *)
Compute mk_netlist (fst (half_adder_s a b)).
Compute mk_netlist (snd (half_adder_s a b)).
(* full_adder : (a^b^c,(a&b)||c&(a^b) *)
Compute signal2str (fst (full_adder_s a b c)).
Compute mk_netlist (fst (full_adder_s a b c)).
Compute mk_netlist (snd (full_adder_s a b c)).
Compute mk_netlist2 (half_adder_s a b).
Compute mk_netlist2 (full_adder_s a b c).

Definition sum_carry := (list tpNetlist * tpNetlist)%type.

(* 生成行波进位加法器的网表 *)
Fixpoint mk_rcadder_netlist_aux (ab: tpPairList_s) (cin: Signal) : list tpNetlist :=
  match ab with 
  | (a, b)::t => 
    let l := mk_netlist2 (full_adder_s a b cin) in
    let '(sum,cout) := full_adder_s a b cin in
        l ++ mk_rcadder_netlist_aux t cout
  | nil => nil
  end.

(* sum0 carry0 sum1 carry1 ... *)
Definition mk_rcadder_netlist_all (ab:tpPairList_s) (cin:Signal) : list tpNetlist :=
  mk_rcadder_netlist_aux (rev ab) cin.

Fixpoint get_odd_elements {A:Type} (lst:list A) : list A :=
  match lst with
  | nil => nil
  | x :: nil => x :: nil
  | x :: _ :: xs => x :: get_odd_elements xs
  end.

Definition mk_rcadder_netlist (ab:tpPairList_s) (cin:Signal) : sum_carry :=
  (* 整个行波进位加法器的sum列表，第一个是最高位的sum *)
  let sum := rev (get_odd_elements (mk_rcadder_netlist_all ab cin)) in
  (* 整个行波进位加法器的carry *)
  let carry := last (mk_rcadder_netlist_all ab cin) [] in
    (sum,carry).

Compute mk_rcadder_netlist [(a,b)] c.
Compute mk_netlist2 (full_adder_s a b c).
(* 2-bit，两个全加器的串联 *)
Compute mk_rcadder_netlist [(Bitv"a1",Bitv"b1");(Bitv"a2",Bitv"b2")] c.
(* 1-bit，相当于一个全加器 *)
Compute mk_rcadder_netlist [(a,b)] c.
Compute mk_netlist2 (full_adder_s a b c). 
(* 2-bit，两个全加器的串联 *)
Compute mk_rcadder_netlist [(Bitv"a1",Bitv"b1");(Bitv"a2",Bitv"b2")] c.








(* ================================================================================= *)
(** ** netlist to Signal *)
(* 未完成 *)
Definition immed2signal (i:tpImmed) : Signal := 
  match i with
  | LowV => Bit0
  | HighV => Bit1
  | SigVar v => Bitv v
 end.

(* (* 把网表中的每个结构转成Signal *) 
Definition tpNetEle2Signal (netEle:tpNetEle) : Signal :=
  match netEle with
  (* 信号直接赋值给string *)
  | ImmedAss (v,i) => Bitv v (immed2signal i)
  (* 信号经过单变量门操作后赋值给string *)
  | GateAss1 (v, (gate,i)) => Letb v (Not1 (immed2signal i))
  | GateAss2 (v, (gate,i,j)) =>
      match gate with
      | AndGate  => Letb v (And2  (immed2signal i)) (immed2signal j)
      | OrGate   => Letb v (Or2   (immed2signal i) (immed2signal j))
      | XorGate  => Letb v (Xor2  (immed2signal i) (immed2signal j))
      | NorGate  => Letb v (Nor2  (immed2signal i) (immed2signal j))
      | NandGate => Letb v (Nand2 (immed2signal i) (immed2signal j))
      | NotGate  => Bit0
      end
  end.


(* 全加器和半加器的网表转Signal *)
Definition n2s (net:list tpNetlist) : list Signal :=
  List.map n2s_aux net.

Compute mk_netlist2 (full_adder_s a b c).
Compute n2s (mk_netlist2 (full_adder_s a b c)). (* 所有的都是Letb *)
Compute (List.map gv (List.map n2s ( mk_netlist2 (full_adder_s a b c)))).
 *)






(* ================================================================================= *)
(** ** netlist to verilog *)
Local Open Scope string_scope.
Definition string_of_tpImmed (immed : tpImmed) : string :=
  match immed with
  | HighV => "1'b1"
  | LowV => "1'b0"
  | SigVar v => v
  end.

Fixpoint netlist_to_verilog_aux (netlist : tpNetlist) : string :=
  match netlist with
  | nil => ""
  | n1 :: nets =>
    match n1 with
    | ImmedAss (output, input) =>
      let verilog_code := "assign " ++ output ++ " = " ++ string_of_tpImmed input ++ ";" in
           verilog_code ++ "
      " ++ netlist_to_verilog_aux nets
    | GateAss1 (output, (gate_type, input)) =>
      let gate_type_str :=
        match gate_type with
        | NotGate => "not"
        | AndGate => "&"
        | OrGate => "|"
        | XorGate => "^"
        | NorGate => "~|"
        | NandGate => "~&"
        end in
      let verilog_code := "assign " ++ output ++ " = " 
          ++ gate_type_str ++ " " ++ string_of_tpImmed input ++ ";" in
           verilog_code ++ "
      " ++ netlist_to_verilog_aux nets
    | GateAss2 (output, (gate_type, input1, input2)) =>
      let gate_type_str :=
        match gate_type with
        | NotGate => "~"
        | AndGate => "&"
        | OrGate => "|"
        | XorGate => "^"
        | NorGate => "~|"
        | NandGate => "~&"
        end in
      let verilog_code := "assign " ++ output ++ " = " 
          ++ string_of_tpImmed input1 ++ " " 
          ++ gate_type_str ++ " " ++ string_of_tpImmed input2 ++ ";" in
           verilog_code ++ "
      " ++ netlist_to_verilog_aux nets
    end
  end.

Fixpoint netlist_to_verilog_aux2 (l:list tpNetlist) : string :=
  match l with 
  | nil => ""
  | l1 :: l' => netlist_to_verilog_aux l1  ++ "
           " ++ netlist_to_verilog_aux2 l'
  end.

Definition netlist_to_verilog (net:sum_carry) : (string * string) :=
  let '(sum,carry) := net in
  let sum_net := netlist_to_verilog_aux2 sum in
  let carry_net := netlist_to_verilog_aux carry in
    (sum_net,carry_net).

(* test *) (* 2bit : sum[0] sum[1] carry *)
Compute netlist_to_verilog (mk_rcadder_netlist l c).






(* ================================================================================= *)
(** ** netlist simulation *)
Definition SigVar2bool (immed : tpImmed) : bool :=
  match immed with
  | LowV => false
  | HighV => true
  | SigVar v => match v with
                | "true" => true 
                | "false" => false
                | _ => false
                end
  end.

Definition evalass (net:tpNetEle) : (string * bool) :=
  match net with
  | GateAss2 (output, (gate,a,b)) =>
    let a1 := SigVar2bool a in
    let b1 := SigVar2bool b in
      match gate with
      | XorGate => (output, xorb a1 b1)
      | AndGate => (output, andb a1 b1)
      | OrGate  => (output, orb  a1 b1)
      | _ => (output, false)
      end
  | _ => ("no", false)   (* 后续需要补充 *)
  end.

Definition env := list (string * bool).

(* 查找变量在环境中的值  *)
Fixpoint lookup (var:string) (e:env) : option bool :=
  match e with
  | [] => None
  | (x,v)::et => if x=?var then Some v else lookup var et
  end.

Definition bool2string (b:bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

(* 从环境中查找值 => 计算 => 把计算的结果添加到环境里 *)
(* 计算一条，得出计算完成后的新的环境
   新的环境中包括原来环境中的内容，和刚刚计算出来的内容
   最终返回新环境 *)
Definition eval_netlist_aux1 (net:tpNetEle) (e:env) : list (string * bool) :=
  match net with
  | GateAss2 (output,(gate,input1,input2)) =>
      match input1,input2 with
      | SigVar v1, SigVar v2 => 
          match lookup v1 e, lookup v2 e with
          | None,None => 
            let result := evalass net in
                 e ++ [result]
          | Some e1, Some e2 =>
            let r1:= SigVar (bool2string e1) in 
            let r2:= SigVar (bool2string e2) in 
            let result:= evalass (GateAss2 (output,(gate,r1,r2))) in
                 e ++ [result]
          | Some e1, None => 
            let r1:= SigVar (bool2string e1) in
            let result:= evalass (GateAss2 (output,(gate,r1,input2))) in
                 e ++ [result]
          | None, Some e2 =>
            let r2:= SigVar (bool2string e2) in 
            let result:= evalass (GateAss2 (output,(gate,input1,r2))) in
                 e ++ [result]
          end
      | SigVar v1, _ =>
        match lookup v1 e with
        | Some e1 => e ++ [evalass (GateAss2 (output,(gate,SigVar (bool2string e1),input2)))]
        | None => e ++ [evalass net]
        end
      | _, SigVar v2 =>
        match lookup v2 e with
        | Some e2 => e ++ [evalass (GateAss2 (output,(gate,input1,SigVar (bool2string e2))))]
        | None => e ++ [evalass net]
        end
      | _, _ => e ++ [evalass net]
      end
  | _ => []  (* 需要补充 *)
  end.

Fixpoint eval_netlist_aux2 (net:tpNetlist) (e:env) : list (string * bool) :=
  match net with
  | n1::n => let new_env := eval_netlist_aux1 n1 e in
               app new_env (eval_netlist_aux2 n new_env)
  | [] => []
  end.

Definition eval_netlist (netlist:tpNetlist) : string * bool :=
  last (eval_netlist_aux2 netlist []) ("None",false).

Fixpoint eval_netlist2 (netlist:list tpNetlist) : list (string * bool) :=
  match netlist with
  | n1::n => (eval_netlist n1) :: eval_netlist2 n
  | [] => []
  end.

Definition eval_netlist_rc (netlist:sum_carry) : list (string * bool) :=
  let '(sum,carry):= netlist in
  let s1 := eval_netlist2 sum in
  let c1 := eval_netlist carry in
    s1 ++ [c1].

Compute eval_netlist2 (mk_netlist2 (full_adder_s (Bitv "true") (Bitv "false") (Bitv "true"))).
(* 仿真结果 : [("Xor2L0", false); ("Or2L0", true)]
   第一个表示求出来的和，为false，第二个表示进位，为true     *)
Compute eval_netlist_rc (mk_rcadder_netlist 
     [(Bitv"true",Bitv"true");(Bitv"true",Bitv"true")] 
      (Bitv "false")).





















