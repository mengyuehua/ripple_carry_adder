Require Import String.
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
Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.
Coercion bool_to_nat : bool >-> nat.

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
Compute s2b (Not1 Bit1).
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
(* signal level adder => boolean level adder *)
Definition adder_s2b (f:tpRcAdder_s) : tpRcAdder_b :=
  fun (ab:tpPairList_b) (c:bool) =>
    let sc := f (bpairs2spairs ab) (b2s c) in
    let sums := fst sc in
    let carry := snd sc in
       (slist2blist sums, s2b carry).

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

Definition simulate_rc_adder (f:tpRcAdder_s) (ab:tpPairList_b) (c:bool) : tpSumCarry_b :=
  let (x,y) := f (bplist2splist ab) (b2s c) in
  (slist2blist x,s2b y).
Compute simulate_rc_adder rc_adder_s [(true,false);(false,true)] true.








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
Definition ck_full_adder_ok
 (full_adder : full_adder_tp) : Prop :=
 forall a b cin : bool,
   let (sum,cout) := full_adder a b cin in 
     a + b + cin = 2 * cout + sum.

Theorem full_adder_b_high_level_verification : 
 ck_full_adder_ok full_adder_b.
Proof.
  unfold ck_full_adder_ok.
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

(* boolean版本的正确性证明 *)
(* 进位的正确性 *)
Theorem rc_adder_carry_red_b : 
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

(* 求和的正确性 *)
Theorem rc_adder_sum_red_b :
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
Theorem rc_adder_carry_red_s : 
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
Theorem rc_adder_sum_red_s : 
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


(* 生成行波进位加法器的verilog代码 *)
(* sum : list Signal => list string *)
Definition Signallist2stringlist (Signal_list:tpList_s) : list string :=
  List.map gv Signal_list.
(* 提取输入中所有变量的名字 *)
Definition input_conv (ab:tpPairList_s) : string :=
  String.concat "," (List.map (fun '(a, b) => gv a ++ "," ++ gv b) ab).
Compute input_conv [(Bitv"a1",Bitv"b1");(Bitv"a2",Bitv"b2")].

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

Fixpoint sum_split (sum:list string) (n:nat) {struct n}: string :=
  let sum_rev := rev sum in
  match n with
  | 0 => ""
  | S m => (sum_split sum m) ++ 
           (mk_fresh "assign sum[" (n-1)) ++ "]" ++ " = " ++ 
           (nth (n-1) sum_rev "unknown") ++ ";" ++ "
        " 
  end.
(* Definition c := Bitv "c".
Definition l := [(Bitv "a1", Bitv "b1"); (Bitv "a2", Bitv "b2")].
Compute sum_split (Signallist2stringlist (fst (rc_adder_s l c))) 2. *)

Definition gv_rc_adder (f:tpRcAdder_s) (ab:tpPairList_s) (c: Signal) : string :=
  let (sum, carry) := f ab c in  
  let n := Datatypes.length ab in
  let ab_list := input_conv ab in
  let c1 := gv c in              
  let sum_list := String.concat "," (List.map gv sum) in
" module rc_adder(                                
             input " ++ ab_list ++ "," ++ c1 ++ ",
             output " ++ "[" ++ (mk_fresh "" (n-1)) ++ ":" ++ (mk_fresh "" 0) ++"] sum ,cout                       
         );" ++ "
        "++ "
        " ++ (sum_split (Signallist2stringlist sum) n) ++
             "assign cout = " ++ (gv carry) ++ ";
                                                
         endmodule  ".

(* test *)
Definition a := Bitv "a".
Definition b := Bitv "b".
Definition c := Bitv "c".
Definition l4 := [(Bitv "a1", Bitv "b1"); (Bitv "a2", Bitv "b2");
                  (Bitv "a3", Bitv "b3"); (Bitv "a4", Bitv "b4")].
Definition l := [(Bitv "a1", Bitv "b1"); (Bitv "a2", Bitv "b2")].
Compute gv_rc_adder rc_adder_s l c.

Compute gv_half_adder half_adder_s a b.
Compute gv_full_adder full_adder_s a b c.


Compute gv_rc_adder rc_adder_s l4 c.





(* ================================================================================= *)
(** ** generate netlist *)
(* direct signal *)
Inductive tpImmed :=
  LowV | HighV | SigVar : string -> tpImmed.
Inductive tpGateNo :=
   NotGate | AndGate | OrGate 
  | XorGate | EqGate | NorGate | NandGate.

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
Definition immed2signal (i:tpImmed) : Signal := 
  match i with
  | LowV => Bit0
  | HighV => Bit1
  | SigVar v => Bitv v
 end.

Fixpoint n2s (ne:list tpNetEle) : Signal :=
  match ne with
  | ImmedAss (v,i)::tl => Letb v (immed2signal i)  (n2s tl) 
 | GateAss1 (v, (NotGate,i))::tl => 
    Letb v (Not1(immed2signal i)) (n2s tl)
 | GateAss2 (v, (XorGate,i,j))::tl => 
    Letb v (Xor2 (immed2signal i) (immed2signal j))  (n2s tl)
 | GateAss2 (v, (AndGate,i,j))::tl => 
    Letb v (And2 (immed2signal i) (immed2signal j))  (n2s tl)
 | GateAss2 (v, (OrGate,i,j))::tl => 
    Letb v (Or2 (immed2signal i) (immed2signal j))  (n2s tl)
 | _ => Bit0
 end.
Compute (List.map n2s ( mk_netlist2 (full_adder_s a b c))).
Compute (List.map gv (List.map n2s ( mk_netlist2 (full_adder_s a b c)))).




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
        | EqGate => "=="
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
        | EqGate => "=="
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





















