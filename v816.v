(*
  Make compatibility of old code with Coq V8.16
*)
Require Export Arith.
Export Nat.

Definition plus_0_l := add_0_l. 
Definition plus_0_r := add_0_r.
Definition mult_0_l := mul_0_l. 
Definition mult_0_r := mul_0_r.
Definition mult_1_l := mul_1_l. 
Definition mult_1_r := mul_1_r.
Definition plus_assoc   := add_assoc. 
Definition plus_comm    := add_comm. 
Definition plus_permute := add_shuffle3.
Definition mult_assoc   := mul_assoc. 
Definition mult_comm    := mul_comm. 
Definition mult_plus_distr_l   := mul_add_distr_l. 
Definition mult_plus_distr_r   := mul_add_distr_r. 
Definition mult_lt_compat_l    := mul_lt_mono_pos_l. 
Definition mult_lt_compat_r    := mul_lt_mono_pos_r. 
Definition mult_le_compat_l    := mul_le_mono_l. 
Definition mult_le_compat_r    := mul_le_mono_r. 
Definition plus_le_compat_l    := add_le_mono_l. 
Definition plus_le_compat_r    := add_le_mono_r. 
Definition plus_lt_compat_l    := add_lt_mono_l. 
Definition plus_lt_compat_r    := add_lt_mono_r. 
Definition plus_lt_compat      := add_lt_mono.

Definition minus_n_O := sub_0_r.

Definition lt_S    := lt_lt_succ_r.
(*
Definition lt_S_n := succ_lt_mono.
Definition lt_n_S := succ_lt_mono.
*)
Definition lt_n_O  := nlt_0_r.
Definition lt_n_Sn := lt_succ_diag_r.
Definition lt_O_Sn := lt_0_succ.
Definition lt_n_Sm_le := lt_succ_r.
Definition lt_le_S    := le_succ_l.
Definition lt_le_weak := lt_le_incl.
Definition lt_plus_trans := lt_le_trans.

Definition le_n_Sn := le_succ_diag_r.
Definition le_lt_n_Sm := lt_succ_r.
Definition le_lt_or_eq := lt_eq_cases.
Definition le_Sn_O := nle_succ_0.
Definition le_n_O_eq  := le_0_r.

Definition neq_O_lt   := neq_0_lt_0.

Lemma lt_S_n : forall n m, S n < S m -> n < m.
intros. rewrite succ_lt_mono. assumption.
Qed.

Lemma lt_n_S: forall n m : nat, n < m -> S n < S m.
intros. rewrite<- succ_lt_mono. assumption.
Qed.

(*
Check Lt.lt_S_n.
Lt.lt_S_n
     : forall n m : nat, S n < S m -> n < m
Check Lt.lt_n_S.
lt_n_S
     : forall n m : nat, n < m -> S n < S m
Check  succ_lt_mono.

succ_lt_mono
     : forall n m : nat, n < m <-> S n < S m
*)
