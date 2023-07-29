(**
    Tactic Definitions and usage examples.

  1. BasicArith: basic arithmetic expression simplification.
  2. F_equal: f(..x..)=f(..y..) => x=y (can be replace by f_equal).
  3. MvLeft_plus a: move a to the left most position in a plus expression.
  4. MvLeft_mult a: move a to the left most position in a mult expression.
  5. RmPlusTm a: remove a from ..+ a +.. = .. + a + ..
  5. RmMultTm a: remove a from ..* a *.. = .. * a * ..
  6. plusGroup (a1+..+an): move a1..an to the left and form (a1+..+an).
  7. caseBool: (a1,..,an): solve arithmetic expression containing booleans a1,..,an.
  8. caseBool2: (a1,..,an): similar to caseBool but ai are of type bool*bool.
  9. listRec var: induction over var; solve base case; apply induction hypothesis.
  10.toFstSnd: let (a,b) := c in e => e[(fst c)/a; (snd c)/b].

   rmS : derive x=y (<,<=) from hypothesis S .. S x = S .. S y. (<,<=)
   autoLe: simplify and prove a < b or a<=b.
   implyLe: prove a<b or a<=b using inequality hypothesis.
   absurdArith: prove <invalid arith cond> -> P.
   locRewrite rule f : rewrite r at first position with head f.
   locRevRewrite rule f : reverse rewrite r at first position with head f.
*)


(**
  Basic arithmetic simplification via equations:
  a+0 => a
  0+a => a
  a-0 => a
  a*1 => a
  1*a => a
  a*0 => 0
  0*a => 0
  a+a => 2*a
*)
Require Import Arith.
Require Import ArithRing.

(* 2013.10.16 *)
Require Import Lia.
Require Import List.

Require Import Bool.
Require Import NArith.
Require Import Mult.
Require Import v816. 
(* 2023 redefine obselete names by new ones. *)
Import Nat.


Lemma a_plus_a : forall (n:nat), n+n = 2*n.
  induction n; simpl; ring.
Qed.

#[export] Hint Rewrite plus_0_l plus_0_r a_plus_a : base_arith.
#[export] Hint Rewrite minus_n_O : base_arith.
#[export] Hint Rewrite mult_0_r mult_0_l mult_1_l mult_1_r : base_arith.

Ltac BasicArith := autorewrite with base_arith.

(** basic arithmetic simplification test. *)
Lemma arith_simp_test : forall (a:nat),
  1 * (a+0) + (a-0) + 1*a = a + a + a.
Proof.
  intro. BasicArith. reflexivity.
Qed.

(** 
   Purpose: produce subequality goal from equality
   Example: (g3 b z x) = (g3 b z y) => x = y 
*) 

Ltac F_equal :=
 match goal with 
  | |- (?x1 ?x2) = (?x1 ?x3) => 
      apply f_equal with (f:=x1); try(auto); F_equal

  | |- (?x1 ?x2 ?x4) = (?x1 ?x3 ?x5) => 
      apply f_equal2 with (f:=x1); try(auto); F_equal

  | |- (?x1 ?x2 ?x3 ?x4) = (?x1 ?x5 ?x6 ?x7) => 
      apply f_equal3 with (f:=x1); try(auto); F_equal

  | |- (?x1 ?x2 ?x3 ?x4 ?x5) = (?x1 ?x6 ?x7 ?x8 ?x9) => 
      apply f_equal4 with (f:=x1); try(auto); F_equal    

  | _ => idtac
 end.



(* F_equal test *)
Lemma F_equal_test2 : forall (A:Set)
  (x y z : A) (g: A->A) (g2 : A->A->A),
  (g x)=y->(g2 z (g x))=(g2 z y).
Proof.
  intros;F_equal.
Qed.

Lemma injective_lists : 
  forall (A:Set) (a : A) (l1 l2 : (list A)),
    l1=l2 -> (a::l1) = (a::l2).
Proof.
  intros.
  rewrite H in |- *.
  reflexivity.
Qed.

(* (a,b) = (c,d) => a=c, b=d *)
Ltac eq_pair :=
  match goal with
    | |- (?x1,?x2) = (?y1,?y2) => (* => x2=y1, x2=y2 *)
      apply injective_projections; simpl; eq_pair
    | |- (?x1 :: ?x2) = (?y1 :: ?y2) =>
      apply injective_lists; simpl; eq_pair
    | _ => try(F_equal)
  end; auto.  (* try solve trivial equalities. *)
      

(** mv term to the left most position. *)

(* 
  move term a to the front of plus expressions. 
  repeated rewritting with rules:
  b + a => a + b
  b+(a+c) => a+(b+c)
  (b+c)+d => b+(c+d)
*)
Ltac MvLeft_plus a :=
  match goal with
    | |- context [(plus a _)]  => fail 0 (* backtracking to next clause. *)
    | |- context [(plus ?b a)] => 
      rewrite (plus_comm b a); MvLeft_plus a
    | |- context [(plus ?b (plus a ?c))] =>  (* => plus a (plus ?b ?c)) *)
      rewrite (plus_permute  b a c); MvLeft_plus a
    | |- context [(plus (plus ?b ?c) ?d)]  => (* plus ?b (plus ?c ?d) *)
      rewrite <- (plus_assoc b c d); MvLeft_plus a           
    | _ => idtac
  end.

Lemma mvLeft_plus_test : forall (a:nat), 
  (a + (1 + 2)) = ((1 + a) + 2).
  intro; MvLeft_plus a; reflexivity.
Qed.

(** remove a term at both sides of an equality. *)
Ltac RmPlusTm a := 
  MvLeft_plus a; apply (f_equal2 plus); [reflexivity | idtac].

Lemma rmPlusTm_test : forall (a:nat), 1 + a + 2 = 1 + 2 + a.
  intro;RmPlusTm a; reflexivity.
Qed.  

(* move term a to the front of mult expressions. *)
Lemma mult_permute : forall n m p, n * (m * p) = m * (n * p).
Proof.
  intros; rewrite (mult_assoc m n p); rewrite (mult_comm m n); auto with arith.
Qed.

Ltac MvLeft_mult a :=
  match goal with
    | |- context [(a * _)]  => fail 0 (* backtracking to next clause. *)
    | |- context [(?b * a)] => 
      rewrite (mult_comm b a); MvLeft_mult a
    | |- context [(?b *(a * ?c))] =>  (* =>  a *(?b * ?c) *)
      rewrite (mult_permute  b a c); MvLeft_mult a
    | |- context [((?b * ?c) * ?d)]  => (* ?b * (?c*?d) *)
      rewrite <- (mult_assoc b c d); MvLeft_mult a           
    | _ => idtac
  end.

Ltac MvRight_mult a :=
  match goal with
    | |- context [(_ * a)]  => fail 0 (* backtracking to next clause. *)
    | |- context [(a * ?b)] => 
      rewrite (mult_comm a b); MvRight_mult a
    | |- context [(?b *(a * ?c))] =>  (* =>  (?b * ?c) * a *)
      rewrite (mult_permute  b a c); rewrite (mult_comm a (b * c)); MvRight_mult a
    | |- context [((?b * ?c) * ?d)]  => (* ?b * (?c*?d) *)
      rewrite <- (mult_assoc b c d); MvRight_mult a           
    | _ => idtac
  end.
(** remove an multiplicant at both sides of an equality. *)
Ltac RmMultTm a :=
  MvLeft_mult a; repeat(rewrite <- mult_plus_distr_l);
  apply (f_equal2 mult); [reflexivity | idtac].

Lemma mvLeft_mult_test : forall (a:nat), 
  (a * (1 * 2)) = ((1 * a) * 2).
  intro; MvLeft_mult a; reflexivity.
Qed.

(** 
  group a = (a1 + .. + an) to the front. For example:
  d + c + e + a + b => (a+b+c)+(d+e)
*)
Ltac plusGroup a :=
  match a with
    | (?y + ?z) + ?x => MvLeft_plus x; plusGroup (y+z); (* => a+(b+(c+(d+e))) *)
      rewrite (fun u => plus_assoc u x)                 (* => ((a+b)+c)+(d+e) *)
    | (?y + ?x) => MvLeft_plus x; MvLeft_plus y; 
      rewrite (fun u => plus_assoc u x)
    | _ => idtac
  end.

Lemma plusGroup_test : forall a b c d e : nat,
  a + b + c + d + e = a + (b + c + (d + e)).
Proof.
  intros; plusGroup (a+b+c); reflexivity.
Qed.

Ltac multGroup a :=
  match a with
    | (?y * ?z) * ?x => MvLeft_mult x; multGroup (y*z); (* => a*(b*(c*(d*e))) *)
      rewrite (fun u => mult_assoc u x)                 (* => ((a*b)*c)*(d*e) *)
    | (?y * ?x) => MvLeft_mult x; MvLeft_mult y; 
      rewrite (fun u => mult_assoc u x)
    | _ => idtac
  end.


(** solve boolean equalities by case analysis over a1..an, 
  other functions may be contained in the expression. 
  input is of the form (a1,..,an).
*)
Ltac caseBool a :=
  match a with
    | ((?y , ?z) , ?x)  => destruct x; caseBool (y , z)
    | (?y , ?x) => destruct x; destruct y
    | _ => idtac
  end; auto.

(* a = (x,..,z), x..z of type bool*bool. apply destruct to all. *)
Ltac caseBool2 a :=
  intros;
  match a with
    | ((?y , ?z) , ?x)  => 
      let x1 := fresh "x1" in let x2 := fresh "x2" in
	caseBool2 (y , z); destruct x as (x1,x2); 
	 destruct x1; destruct x2

    | (?y , ?x) => 
      let x1 := fresh "x1" in let x2 := fresh "x2" in
      let y1 := fresh "y1" in let y2 := fresh "y2" in
	destruct x as (x1,x2); destruct y as (y1,y2);
	destruct x1; destruct x2;
	  destruct y1; destruct y2
    | ?x => (* when x is a variable *)
      let x1 := fresh "x1" in let x2 := fresh "x2" in
	 destruct x as (x1,x2); destruct x1; destruct x2

  end; auto.

(** conditional rewriting example. *)


Lemma S_to_plus_one : forall (n:nat), (S n)=n+1.
  intro; ring.
Qed.

Ltac S_to_plus_simpl :=
  match goal with
  | |-  context [(S ?X1)] =>
      match X1 with
      | 0%nat => fail 1
      | ?X2 => rewrite (S_to_plus_one X2); S_to_plus_simpl
      end
  | |- _ => idtac
  end.

(* test lemma for S_to_plus_simpl *)
Lemma S_to_plus_simpl_test : forall n:nat,
  (S 0) + (S n) = (S 0) + n + 1.
Proof.
  intro; S_to_plus_simpl; reflexivity.
Qed.

(* elimination of let (a,b) := c *)
(** let (a,b) := c in e => e[(fst c)/a; (snd c)/b] *)
Ltac toFstSnd :=
  match goal with
    | |- context [(match ?c with (_,_) => _ end)] 
      => rewrite (surjective_pairing c); toFstSnd
    | _ => idtac
  end.


Lemma letPairToFstSnd_test : forall (f: nat->nat*nat) (x:nat),
  let (a,b) := (f x) in 
    a+b = (fst (f x)) + (snd (f x)).
Proof.
  intros.
  rewrite (surjective_pairing (f x)).
(*  toFstSnd. will take the role of surjective_pairing. *)
  simpl; reflexivity.
Abort.

Lemma letPairToFstSnd_test : forall (f: nat->nat*nat) (x:nat),
  let (a,b) := (f x) in 
    a+b = (fst (f x)) + (snd (f x)).
Proof.
  intros.
  toFstSnd.
  simpl; reflexivity.
Qed.

Ltac letPair :=
  match goal with
    | |- context [(match ?c with (_,_) => _ end)] 
      => destruct c; letPair
    | |- _ => idtac
  end.

Lemma pair_eq_left : forall (A B : Set) (a c : A) (b d : B),
  (a,b) = (c,d) -> a=c.
Proof.
  intros.
  assert (fst (a, b) = fst (c, d)).
  rewrite H in |- *.
  auto.
  simpl in H0.
  assumption.
Qed.

Lemma pair_eq_right : forall (A B : Set) (a c : A) (b d : B),
  (a,b) = (c,d) -> b=d.
Proof.
  intros.
  assert (snd (a, b) = snd (c, d)).
  rewrite H in |- *.
  auto.
  simpl in H0.
  assumption.
Qed.

(** generate hypothesis a=c,b=d from (a,b)=(c,d) and rewrite *)
Ltac pairSplitH :=
  match goal with
    | [h : (?a , ?b) = (?c , ?d) |- _ ] =>
      let h1 := fresh "fstH" in
	let h2 := fresh "sndH" in
	  assert(h1 : a=c);  (* derive new hypothesis fstH : a=c *)
	    [apply pair_eq_left in h; assumption | idtac];
	  assert(h2 : b=d);  (* derive new hypothesis sndH : b=d *)
	    [apply pair_eq_right in h; assumption | idtac];
	  clear h;
	  repeat(rewrite <- h1); (* in general, equalities are of the form var = expression *)
	  repeat(rewrite <- h2)
    | _ => idtac
  end.

Lemma pairSplitH_test : forall (A:Set) (a b c d : A), 
  (a,b)=(c,d) -> (b,a)=(d,c).
Proof.
  intros.
  pairSplitH.
  reflexivity.
Qed.

(** do intros but put the input var at the last. *)
Ltac introIH ih := intros until ih; try(intro after ih).
    
(** simple list function induction, input is induction var. *)
Ltac listRec a :=
  try(introIH a); 
  induction a as [| hd tl IH]; simpl; try(ring); auto; 
    try(simpl; 
      [(letPair; simpl in * |- *; rewrite IH) || (* e.g. sum_len *)
	rewrite IH; letPair];          (* e.g. split_fst_snd *)
      simpl;   auto).


(* listRec test example *)    
Definition mapfst (A:Set) (ab:(list (A*A))) : (list A)
  := map (A:=A*A) (B:=A) (fst (A:=A) (B:=A)) ab. (* type arguments supplied explicitly *)

Lemma mapfst_len_test : forall (A:Set) (ab:(list (A*A))),
  length (mapfst A ab) = length ab.
Proof.
  listRec ab.
(* induction ab; simpl; try(ring); auto.*)
Qed.

(* similar to listRec but deal with equality of pairs. *)
Ltac listProdRec a :=  	  
  intros; induction a as [| hd tl IH]; auto; 
    simpl;  letPair; pairSplitH; auto.

(* sample usage of listProdRec can be found in listext.v *)

(** reverse the intro operation. *)
Ltac revIntros :=
  match goal with
    [ h: ?x |- _ ] => generalize h; clear h; revIntros
    | _ => idtac
  end.

(** run tactic in the body of universally quantified proposition. *)
Ltac rewriteForall tac :=
  intros; tac; revIntros.

(** derive x=y (<,<=) from hypothesis S .. S x = S .. S y. (<,<=)*)
Ltac rmS h :=
  match type of h with
    | S ?x = S ?y =>
      let h0 := fresh "HS" in
	assert(h0 : x=y); 
	  [apply eq_add_S; assumption | clear h; rmS h0]
    | S ?x < S ?y =>
      let h0 := fresh "HS" in
	assert(h0 : x<y); 
	  [apply lt_S_n; assumption | clear h; rmS h0]
    | S ?x <= S ?y =>
      let h0 := fresh "HS" in
	assert(h0 : x<=y); 
	  [apply le_S_n; assumption | clear h; rmS h0]
    | _ => try(assumption)
  end.

(*
Lemma mult_lt_compat_l : forall n m p, 
  n < m -> 0 < p -> p * n < p * m.
Proof.

  intros n m p H.
  rewrite mult_comm in |- *.
  rewrite (mult_comm p) in |- *.
  intro;  apply mult_lt_compat_r; auto.
Qed.
*)
(** simplify or prove a < b or a<=b, can be replaced by lia. *)
Ltac autoLe :=
  match goal with
    | |- 0 < S _ => apply lt_O_Sn
    | |- ?x < S ?x => apply lt_n_Sn
    | |- ?x <= S ?x => apply le_n_Sn
    | |- ?x <= ?x => apply le_refl
    | |- S ?x < S ?y => apply lt_n_S; autoLe
    | |- S ?x <= S ?y => apply le_n_S; autoLe
    | |- ?p + ?m < ?p + ?n =>  apply plus_lt_compat_l;autoLe
    | |- ?m + ?p < ?n + ?p =>  apply plus_lt_compat_r;autoLe
    | |- ?p + ?m <= ?p + ?n =>  apply plus_le_compat_l;autoLe
    | |- ?m + ?p <= ?n + ?p =>  apply plus_le_compat_r;autoLe
    | |- ?p + ?m < ?q + ?n =>  apply plus_lt_compat; autoLe
    | |- ?p * ?m < ?p * ?n =>  apply mult_lt_compat_l;autoLe
    | |- ?m * ?p < ?n * ?p =>  apply mult_lt_compat_r;autoLe
    | |- ?p * ?m <= ?p * ?n =>  apply mult_le_compat_l;autoLe
    | |- ?m * ?p <= ?n * ?p =>  apply mult_le_compat_r;autoLe

    | |- ?x < ?y + ?z => apply lt_plus_trans;autoLe
    | _ => try(assumption)
  end.

(** prove <=, < under hypothesis *)
Ltac implyLe :=
  match goal with
    | h : ?x < ?y |- ?x <= ?y     => apply lt_le_weak; apply h
    | h : ?x <= ?y |- ?x < S ?y   => apply le_lt_n_Sm; apply h
    | h : ?x <  ?y |- ?x < S ?y   => apply lt_S; apply h
    | h : S ?n < S ?m |- ?n < ?m  => apply lt_S_n; apply h
    | h : ?n < ?m |- S ?n < S ?m  => apply lt_n_S; apply h
    | h : ?n < ?m |- S ?n < S ?m  => apply le_n_S; apply h
    | h : 0 <> ?n |- 0 < ?n       => apply neq_O_lt; apply h
    | h : ?n < S ?m |- ?n <= ?m   => apply lt_n_Sm_le; apply h
    | h : ?n <= ?m |- ?n <= S ?m  => apply le_S ; apply h

    | h : _ -> ?x < ?y |- ?x <= ?y     => apply lt_le_weak; apply h
    | h : _ -> ?x <= ?y |- ?x < S ?y   => apply le_lt_n_Sm; apply h
    | h : _ -> ?x <  ?y |- ?x < S ?y   => apply lt_S; apply h
    | h : _ -> S ?n < S ?m |- ?n < ?m  => apply lt_S_n; apply h
    | h : _ -> ?n < ?m |- S ?n < S ?m  => apply lt_n_S; apply h
    | h : _ -> ?n < ?m |- S ?n < S ?m  => apply le_n_S; apply h
    | h : _ -> 0 <> ?n |- 0 < ?n       => apply neq_O_lt; apply h
    | h : _ -> ?n < S ?m |- ?n <= ?m   => apply lt_n_Sm_le; apply h
    | h : _ -> ?n <= ?m |- ?n <= S ?m  => apply le_S ; apply h

    | h1 : ?a < ?b, h2 : ?b < ?c |- ?a < ?c => 
      apply (lt_trans a b c); assumption
    | h1 : ?a <= ?b, h2 : ?b <= ?c |- ?a <= ?c => 
      apply (le_trans a b c); assumption
    | h1 : ?a < ?b, h2 : ?b <= ?c |- ?a < ?c => 
      apply (lt_le_trans a b c); assumption
    | h1 : ?a <= ?b, h2 : ?b < ?c |- ?a < ?c => 
      apply (le_lt_trans a b c); assumption
    | _ => idtac
  end.

(** prove the goal from a false hypothesis a<b. *)
Ltac absurdLe h :=
  match type of h with
    | ?x < ?x => 
      absurd(x<x); [apply lt_irrefl| assumption]
    | ?x < 0 => 
	absurd(x<0); [apply lt_n_O| assumption]
    | S ?x <= 0 => 
        absurd(S x <= 0); [ apply le_Sn_O | assumption]
    | S ?x < S ?y => 
      let h0 := fresh "HL" in
	assert(h0 : x<y); absurdLe h0
    | _ => try(assumption)
  end.

(** prove goal from false arithmetic hypothesis cond -> goal. *)
Ltac absurdArith :=
  let h0 := fresh "HL" in
    intro h0;  
      let tp := type of h0 in
	absurd(tp); [ lia | assumption ].
(*
  Example:
   S (S (length l0)) = 1 -> dp0 (a :: l0) ao = dp1 0 ((a :: l0) :+ ao)
  < absurdArith.
*)

Ltac absurdRefl :=
  let h0 := fresh "HL" in
    intro h0;  
      let tp := type of h0 in
	absurd(tp); [ reflexivity | assumption ].


(* Require Import Lt. *)
(* intros a l with fresh names. *)
Ltac intro_a_l :=
  let a := fresh "a" in let l := fresh "l" in intros a l.

(** i < length l -> P(l) => P(ai::..::a1::l') *)
Ltac rmLen := (* need Omega to work on. *)
  match goal with
    | |- S ?x < S ?y -> _ => 
      let h := fresh "H" in intro h;
      let h0 := fresh "HS" in
	assert(h0 : x<y); 
	  [apply lt_S_n; assumption | clear h; rmLen];
	  generalize h0; clear h0; rmLen

    | |- _ < length (_::_) -> _ => simpl length; rmLen
      
    | |- S ?i < length ?l -> _ => 
        case l; simpl length; [absurdArith | intro_a_l]; rmLen

    | |- 0 < length ?l -> _ =>
        case l; simpl length; [absurdArith | intro_a_l]; rmLen        

    | |- 0 < S _ -> _ => let h:=fresh "H" in intro h; clear h

    | _ => idtac
  end.

(* example:  1 < length l -> P l => P (a::a0::l1) *)

(** two steps case analysis: l = nil,a::nil,others. *)
Ltac case2 l l0 := intros;case l;auto;intros;case l0;auto;intros.

(** apply a tactic until there are no progress. *)
Ltac while tac := repeat(progress(try(tac))).


(** use rule r to  rewrite the subterm with head f at first location. *)
Ltac locRewrite r f :=
  let f0 := fresh "f0" in
    set(f0 := f);  unfold f0 at 1; rewrite r; 
      unfold f0; clear f0.

(** use rule r to reverse rewrite the subterm with head f at first location. *)
Ltac locRevRewrite r f :=
  let f0 := fresh "f0" in
    set(f0 := f);  unfold f0 at 1; rewrite <- r; 
      unfold f0; clear f0.

