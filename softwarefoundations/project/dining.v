Require Import Nat.
Require Import List.
Require Import Omega.
Require Import Coq.Logic.FunctionalExtensionality.
(* Problem: Starvation freedom is not formally defined! *)
(* Problem: Algebra of traces being used is not defined *)
(* how do we formally state philosopher does not remain hungry forever? *)
(* Problem: it is untrue that we have startvation freedom. *)

(* Problem: the clock is extremely unphysical: it is basically a collection of dirac deltas. What
   is the point of this representation? I don't understand why we even need this *)

(* From here on, we will not explicitly model the clock or its composition with
systems. Instead, we assume that all systems we design are implicitly clocked
and there is one global clock that drives all the subsystems of a system:

This is completely underspecified. In particular, what does it mean for
there to be a global clock that drives all the subsystems? I would have expected
to see some kind of 'transformer' that takes a system and then clocks it!

Also note that in the tabuada regime, to speak of a subsystem is meaningless:
we don't really know _what_ the subsystems are, since we are allowed to compose anything
with anything else. ie, tabuada composition is not an algebraic data type
that we can decompose on!
*)

(* 2.1: system specifcation *)
Record system (X: Set) (U: Set) := mksystem { isx0: X -> Prop; trans: X -> U -> X -> Prop }.


(* 2.2: system composition *)
Definition tabuada_start {X Y: Type} (isx0: X -> Prop) (isy0: Y -> Prop) (x: X * Y): Prop :=
  isx0 (fst  x) /\ isy0 (snd x).

(* transition fn for tabuada composition *)
Definition tabuada_trans {X Y: Type} {UX UY: Type} (connect: X*Y->UX*UY->Prop) (transx: X -> UX -> X -> Prop) (transy: Y -> UY -> Y -> Prop)
           (s: X*Y) (u: UX*UY) (s': X*Y): Prop :=
  transx (fst s) (fst u) (fst s') /\
  transy (snd s) (snd u) (snd s') /\
  (connect s u).

(* tabuada connection new system *)
Definition tabuada {X Y UX UY: Set} (sx: system X UX) (sy: system Y UY) (connect: X*Y->UX*UY->Prop): system (X*Y) (UX*UY) :=
  mksystem (X*Y) (UX*UY) (tabuada_start (isx0 X UX sx) (isx0 Y UY sy))
           (tabuada_trans connect (trans X UX sx) (trans Y UY sy)).

Inductive star := mkstar.



(* 3.1: Philosopher as autonomous NDTM *)
(* We rename Act into the *)
Inductive the := t | h | e.
Inductive trans31: the -> star -> the -> Prop := mktransphil31: forall (x x': the), trans31 x mkstar x'.
Definition phil31 := mksystem the star (fun x => x = t) trans31.

(* 3.2: Choice determinism *)
Definition next(s: the): the :=
  match s with
  | t => h | h => e | e => t
  end.

Inductive choice := choice_0 | choice_1.
Definition trans32fn (s: the) (c: choice): the :=
  match c with
  | choice_0 => s | choice_1 => next s
  end.
Definition isthinking (s: the): Prop := s = t.
Definition phil32 := mksystem the choice  isthinking  (fun s u s' => trans32fn s u = s').

(* Problems: Proposition 3.1 (end of page 15). B \omega ( Q ) = B \omega ( P ) . 
   - The set B w has not been defined before. Indeed, this statement is meaningless on its own
     without guessing.
   - 
*)

(* 3.3 Interfacing control *)
Inductive cmd := cmd_pass | cmd_bang0 | cmd_bang1.
(* composition *)
Definition trans33fn (s: the) (u: cmd * choice): the :=
  match u with
  | (cmd_pass, ch) => trans32fn s ch
  | (cmd_bang0, _) => s
  | (cmd_bang1, _) => next s
  end.

Definition phil33 := mksystem the (cmd * choice) isthinking  (fun s u s' => trans33fn s u = s').

(* 3.4 Controller *)
Definition ispass (c: cmd):Prop := c = cmd_pass.
Definition trans34fn (s: cmd) (u: the): cmd :=
  match u with
  | h => cmd_bang1 | e => cmd_pass | t => cmd_pass
  end.
Definition controller34 := mksystem cmd the ispass (fun s u s' => trans34fn s u = s').

(* feedback composition: we shall define tabuada composition here *)
Check (phil33).
(*
Inductive connect34: the * cmd ->
                     cmd * choice * the -> Prop :=
| mkconnect34: forall (sx: the) (sy: cmd) (ch: choice), connect34 (sx, sy) ((sy, ch  ), sx).
*)


Definition connect34 (xy: the * cmd)
                        (ux_uy: cmd * choice * the): Prop :=
  (fst xy) = (snd ux_uy) /\ (snd xy = fst (fst ux_uy)).

(* This will do the wrong thing, since it will connect my *current state* with the *transition action*?
   but the transition action is attempting to dictate my *next state* *)
Definition system35 := tabuada phil33 controller34 connect34.


(* relation is checked upto: [0-1, 1-2, ...(n-1)-n] *)
(* states, choices *)
Inductive ValidTrace {X U: Set} (s: system X U) (xs: nat -> X) (us: nat -> U): nat -> Prop :=
| Start: forall  (VALID: (isx0 X U s) (xs 0)) , ValidTrace s xs us 0
| Cons: forall (n: nat) (TILLN: ValidTrace s xs us n) (ATN: trans X U s (xs n) (us n) (xs (S n))),
    ValidTrace s xs us (S n).

Hint Unfold tabuada_start.

(* Table 2 reproduction *)
Definition states_table_2 (n: nat):  the * cmd :=
  match n with
  | 0 => (t, cmd_pass)
  | 1 => (h, cmd_pass)
  | 2 => (h, cmd_bang1)
  | 3 => (e, cmd_bang1)
  | 4 => (t, cmd_pass) 
  | _ => (t, cmd_pass) (* default *)
  end.

Definition trans_table_2 (n: nat): cmd * choice * the :=
  match n with
  | 0 => (cmd_pass, choice_1, t)
  | 1 => (cmd_pass, choice_0,h) 
  | 2 => (cmd_bang1, choice_0,h) 
  | 3 => (cmd_bang1, choice_0,e) 
  | _ => (cmd_pass, choice_1, t) (* default *)
  end.
    
  
Example valid_trace_table2_step0:
  ValidTrace system35 states_table_2 trans_table_2 0.
Proof.
  repeat (try constructor; simpl; try apply valid_trace_table2_step1; try apply tabuada_start).
Qed.

Example valid_trace_table2_step1   : ValidTrace system35 states_table_2 trans_table_2 1.
Proof.
  repeat (try constructor; simpl; try apply valid_trace_table2_step1; try apply tabuada_start).
Qed.

Example valid_trace_table2_step2   : ValidTrace system35 states_table_2 trans_table_2 2.
Proof.
  repeat (try constructor; simpl; try apply valid_trace_table2_step1).
Qed.

Example valid_trace_table2_step3   : ValidTrace system35 states_table_2 trans_table_2 3.
Proof.
  repeat (try constructor; simpl; try apply valid_trace_table2_step1).
Qed.

Example valid_trace_table2_step4   : ValidTrace system35 states_table_2 trans_table_2 4.
Proof.
  repeat (try constructor; simpl; try apply valid_trace_table2_step1).
Qed.

(* Table 2 has been checked.  *)


(* section 3.7: slower philosopher *)
Inductive maybe (T: Type) := just: T -> maybe T | nothing: maybe T.

(* TODO: understand this ordering *)
(* PROBLEM: in paper, this is written as "pattern matching syntax" due to the overlapping
   patterns. This should be _very clearly stated_ *)
Definition trans37fnDEPR (s: the) (u: cmd * maybe choice): the :=
  match u with
  | (_, nothing _) => s (* this looks fishy! what if I send !0 / !1? I don't trust this :(. Indeed, moving this down 
                           to be below cmd_bang0, cmd_bang1 breaks things *)
  | (cmd_bang0, _) => s
  | (cmd_bang1, _) => next s
  | (cmd_pass, just _ ch) => trans32fn s ch

  end.

Print trans37fnDEPR.

(* PROBLEM: due to composition, this needs to be carried as tuples.
   pattern matching is hell *)
Definition trans37fn (s: the) (u: cmd * maybe choice): the :=
    match fst u with
    | cmd_bang0 => s
    | cmd_bang1 => match snd u  with | just _ _ => next s | nothing _ => s end
    | cmd_pass => 
      match snd u   with
      | nothing _ => s (* this looks fishy! what if I send !0 / !1? I don't trust this :(. Indeed, moving this down 
                           to be below cmd_bang0, cmd_bang1 breaks things *)
      | just _ ch   => trans32fn s ch
    end
  end.

(* We will use this to make sure that on the even cycle, our choice
  is always nothing *)
Lemma trans37_choice_nothing:
  forall (s: the) (u: cmd * maybe choice)
         (CHOICENOTHING: snd u = nothing choice),
    trans37fn s u = s.
Proof.
  intros.
  unfold trans37fn.
  destruct u; destruct c; simpl in *; subst; auto.
Qed.

Lemma trans37_cmd_pass_trans32:
  forall (s: the) (u: cmd * maybe choice)
         (c: choice) (C: snd u = just choice c)
         (CMD_PASSS: fst u = cmd_pass),
    trans37fn s u = trans32fn s c.
Proof.
  intros.
  unfold trans37fn.
  destruct u; destruct c; simpl in *; subst; auto.
Qed.

Definition phil37 := mksystem the (cmd * maybe choice) isthinking  (fun s u s' => trans37fn s u = s').



(* 3.8: the new interconnect *)
(* TODO: make this modular; call it connect_slowed_left *)
(* 
Inductive connect38: the * cmd ->
                     cmd * (maybe choice) * the -> Prop :=
| mkconnect38: forall (sx: the) (sy: cmd) (mch: maybe choice), connect38 (sx, sy) ((sy, mch), sx).
*)


Definition connect38 (xy: the * cmd)
                     (ux_uy: cmd * (maybe choice) * the): Prop :=
  (fst xy) = (snd ux_uy) /\ (snd xy = fst (fst ux_uy)).
  

(* PROBLEM: we assume that the choice 
input to the philosopher alternates between
absent (\bot) and present (0 or 1). Why
is this legal? *)
Definition system38 := tabuada phil37 controller34 connect38.

(* Verify table 3 *)
Definition states_table_3 (n: nat):  the * cmd :=
  match n with
  | 0 => (t, cmd_pass)
  | 1 => (t, cmd_pass)
  | 2 => (h, cmd_pass)
  | 3 => (h, cmd_bang1)
  | 4 => (e, cmd_bang1) 
  | 5 => (e, cmd_pass) 
  | 6 => (e, cmd_pass) 
  | 7 => (e, cmd_pass) 
  | 8 => (e, cmd_pass) 
  | 9 => (e, cmd_pass) 
  | 10 => (t, cmd_pass) 
  | _ => (t, cmd_pass) (* default *)
  end.

Definition trans_table_3 (n: nat): cmd * maybe choice  * the :=
  match n with
  | 0 => (cmd_pass,  nothing _,       t)
  | 1 => (cmd_pass,  just _ choice_1, t) 
  | 2 => (cmd_pass,  nothing _,       h) 
  | 3 => (cmd_bang1, just _ choice_0, h) 
  | 4 => (cmd_bang1, nothing _,       e) 
  | 5 => (cmd_pass,  just _ choice_0, e) 
  | 6 => (cmd_pass,  nothing _,       e) 
  | 7 => (cmd_pass,  just _ choice_0, e) 
  | 8 => (cmd_pass,  nothing _,       e) 
  | 9 => (cmd_pass,  just _ choice_1, e) 
  |10 => (cmd_pass,  nothing _,       t) 
  | _ => (cmd_pass,  nothing _,      t) (* default *)
  end.

Example valid_trace_table3_step0: ValidTrace system38 states_table_3 trans_table_3 0.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step1: ValidTrace system38 states_table_3 trans_table_3 1.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step2: ValidTrace system38 states_table_3 trans_table_3 2.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step3: ValidTrace system38 states_table_3 trans_table_3 3.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step4: ValidTrace system38 states_table_3 trans_table_3 4.
Proof.
  repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start).
Qed.

Example valid_trace_table3_step5: ValidTrace system38 states_table_3 trans_table_3 5.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step6: ValidTrace system38 states_table_3 trans_table_3 6.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

(* elided 7, 8 *)
Example valid_trace_table3_step9: ValidTrace system38 states_table_3 trans_table_3 9.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step10: ValidTrace system38 states_table_3 trans_table_3 10.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.


(* Helper:  rewrite ss in terms of ts for cmd *)
Lemma system38_s_cmd_to_t_cmd: 
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE: ValidTrace system38 ss ts (S n)),
    fst (fst (ts n)) = snd(ss n).
Proof.
  intros.
  inversion TRACE as [TRACE1 | npred TRACE1 AT1].
  subst.
  inversion AT1 as [AT11 [AT12 AT13]].
  set (s1 := ss 1) in *.
  destruct s1 as [s1_the s1_cmd].
  set (t1 := ts 1) in *.
  destruct t1 as [[t1_cmd t1_mchoice] t1_the].
  simpl in *.
  inversion AT13; simpl in *.
  rewrite H0. auto.
Qed.

(* Helper:  rewrite ss in terms of ts for the *)
Lemma system38_s_the_to_t_the: 
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE: ValidTrace system38 ss ts (S n)),
    snd (ts n) = fst (ss n).
Proof.
  intros.
  inversion TRACE as [TRACE1 | npred TRACE1 AT1].
  subst.
  inversion AT1 as [AT11 [AT12 AT13]].
  set (s1 := ss 1) in *.
  destruct s1 as [s1_the s1_cmd].
  set (t1 := ts 1) in *.
  destruct t1 as [[t1_cmd t1_mchoice] t1_the].
  simpl in *.
  inversion AT13; simpl in *.
  rewrite H. auto.
Qed.

(* Helper: in an even state, if we feel hungry, then the controller
   will order a !1 *)
Lemma system38_phil_hungry_then_next_controller_bang1:
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SN: ValidTrace system38 ss ts (S n))
         (HUNGRY: fst (ss n) = h),
    snd (ss (S n)) = cmd_bang1.
Proof.
  intros.
  inversion TRACE_SN as [_ | n' TRACE_N AT_N]; subst.
  assert (TSN_HUNGRY: snd (ts n) = h). rewrite <- HUNGRY. apply system38_s_the_to_t_the; auto.
  inversion AT_N as [AT_N_PHIL [AT_N_CONTROL AT_N_TABU]].
  inversion AT_N_CONTROL as [AT_N_CONTROL_TRANS].
  rewrite TSN_HUNGRY.
  simpl.
  reflexivity.
Qed.


(* Helper: in an even state, if we feel hungry, then we wil continue to be hungry *)
Lemma system38_phil_even_state_next_state:
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SN: ValidTrace system38 ss ts ((S n)))
         (BOTTOM_EVEN: forall (i: nat) (IEVEN: even i = true), snd (fst (ts i)) = nothing choice)
         (NEVEN: even n = true),
    fst (ss (S n)) = fst (ss n).
Proof.
  intros.
  inversion TRACE_SN as [_ | n' TRACE_N AT_N]; subst.
  inversion AT_N as [AT_N_PHIL [AT_N_CONTROL AT_N_TABU]].
  inversion AT_N_PHIL as [AT_N_PHIL_TRANS].
  apply trans37_choice_nothing.
  apply BOTTOM_EVEN.
  apply NEVEN.
Qed.

(* Helper: reason about even/odd *)
Lemma even_n_odd_Sn: forall (n: nat), (even n = true) <-> (odd (S n) = true).
Proof.
  intros; split.
  - intros; rewrite  Nat.odd_succ; auto.
  - intros. rewrite <- Nat.odd_succ; auto.
Qed.

(* Helper: reason about even/odd *)
Lemma odd_n_even_Sn: forall (n: nat), (odd n = true) <-> (even (S n) = true).
Proof.
  intros; split.
  - intros; rewrite  Nat.even_succ; auto.
  - intros. rewrite <- Nat.even_succ; auto.
Qed.

(* Helper: Prove that the state at an odd time point is the same as the previous state  *)
Lemma system38_phil_odd_state_prev_state:
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SN: ValidTrace system38 ss ts ((S n)))
         (BOTTOM_EVEN: forall (i: nat) (IEVEN: even i = true), snd (fst (ts i)) = nothing choice)
         (SNODD: odd (S n) = true),
    fst (ss n) = fst (ss (S n)).
Proof.
  intros.
  inversion TRACE_SN as [_ | n' TRACE_N AT_N]; subst.
  inversion AT_N as [AT_N_PHIL [AT_N_CONTROL AT_N_TABU]].
  inversion AT_N_PHIL as [AT_N_PHIL_TRANS].
  rewrite trans37_choice_nothing; auto.
  apply BOTTOM_EVEN. apply even_n_odd_Sn; auto.
Qed.


(* TODO: write down assumption that philosopher on odd times will always send state *)
(* Helper: Prove that the state after an odd point is the transfer function aplied *)

Lemma system38_odd_state_next_phil_state:
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SN: ValidTrace system38 ss ts ((S n)))
         (BOTTOM_EVEN: forall (i: nat) (IEVEN: even i = true), snd (fst (ts i)) = nothing choice)
         (SNODD: odd n = true),
    fst (ss (S n)) = trans37fn  (fst (ss n)) (fst (ts n)). 
Proof.
  intros.
  inversion TRACE_SN as [_ | n' TRACE_N AT_N]; subst.
  inversion AT_N as [AT_N_PHIL [AT_N_CONTROL AT_N_TABU]].
  inversion AT_N_PHIL as [AT_N_PHIL_TRANS].
  reflexivity.
Qed.



(* HELPER *)
Lemma system38_phil_not_hungry_then_next_controller_pass:
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SN: ValidTrace system38 ss ts (S n))
         (NOTHUNGRY: fst (ss n) <> h),
    snd (ss (S n)) = cmd_pass.
Proof.
  intros.
  inversion TRACE_SN as [_ | n' TRACE_N AT_N]; subst.
  assert (TSN_NOT_HUNGRY: snd (ts n) <> h). erewrite  system38_s_the_to_t_the; auto; try (apply NOTHUNGRY); try (apply TRACE_SN).
   
  inversion AT_N as [AT_N_PHIL [AT_N_CONTROL AT_N_TABU]].
  inversion AT_N_CONTROL as [AT_N_CONTROL_TRANS].

  set (tsn := ts n) in *.
  destruct tsn as [[tsn_cmd  tsn_mchoice]  tsn_the].
  simpl in *.
  destruct tsn_the; try contradiction; auto.
Qed.




(* 3.11: correctness *)
(* in an even state, if we DO NOT feel hungry, then the controller
   will order a pass *)

(* PROBLEM: if a /= h, then a' = f_P ( a, b ):
   Should be: if a /= h, then a' = f_P ( a, b' ):
                                
   The statement assumes that a choice called b exists. That is, 
   it assumes that we will not have `nothing` choice on the odd states.
   This is not made explicit
    PAST: n [even]
       |
       v 
      CURRENT: S n = n + 1 [odd]
       |
      EVEN S n = n + 2 [even]
       | 
      NEXT ODD: S (S (S n))) = n + 3 [odd]

   reason about past. 
   - KEY LEMMA: states only change from ODD -> EVEN transition.

   - Since n is even , it will have same state (n+1)
   - since we are not hungry at (n+1), we are not hungry at (n)
   - since we are not hungry at (n), controller will emit (pass)
   - this means that at (n+1), we can apply our action.
   - at (n+2), we will have applied our action.
   - at (n+3), we will have the same state as (n+2).
 *) 
Lemma system_38_phil_not_hungry_then_next_philo_choice:
  forall (n: nat)
         (ss: nat -> the * cmd)
         (c: choice) 
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SSSN: ValidTrace system38 ss ts (S (S (S n))))
         (NOTHUNGRY: fst (ss (S n)) <> h)
         (CHOICE: snd (fst (ts (S n))) = just choice c)
         (NEVEN: even n = true)
         (BOTTOM_EVEN: forall (i: nat) (IEVEN: even i = true), snd (fst (ts i)) = nothing choice),
    fst (ss (S (S  (S n)))) = trans32fn (fst (ss (S n))) c.
Proof.
  intros.
  assert (STATE_PREV: fst (ss n) = fst (ss (S n))).
  erewrite system38_phil_odd_state_prev_state; eauto.
  inversion TRACE_SSSN. inversion TILLN. auto.
  apply even_n_odd_Sn; auto.
  assert (STATE_PREV_NOT_HUNGRY: fst  (ss n) <> h).
  rewrite STATE_PREV. exact NOTHUNGRY.
  assert (CMD_CUR_PASS: snd (ss (S n)) = cmd_pass).
  eapply system38_phil_not_hungry_then_next_controller_pass; eauto.
  inversion TRACE_SSSN. inversion TILLN. exact TILLN0.

  assert (CUR_TO_NEXT_TRANSITION_TRANS37: fst (ss (S (S n))) = trans37fn  (fst (ss (S n))) (fst (ts (S n)))).
  apply system38_odd_state_next_phil_state; auto.
  inversion TRACE_SSSN; auto.
  apply even_n_odd_Sn; auto.

  assert (CUR_TO_NEXT_TRANSITION_TRANS32: fst (ss (S (S n))) = trans32fn  (fst (ss (S n))) c).
  erewrite <- trans37_cmd_pass_trans32; eauto.
  rewrite <- CMD_CUR_PASS.
  eapply system38_s_cmd_to_t_cmd; eauto.
  inversion TRACE_SSSN; auto.

  assert (NEXT_TO_NEXT_NEXT: fst (ss (S (S (S n)))) = fst (ss (S (S n))) ).
  eapply system38_phil_even_state_next_state; eauto.
  congruence.
Qed.

  

(*
    PAST: n [even] -> hungry, will send !1 to current.
       |
       v 
      CURRENT: S n = n + 1 [odd] -> hungry, !1 sent, will transition.
       |
      EVEN S n = n + 2 [even] -> transitioned to eating.
       | 
      NEXT ODD: S (S (S n))) = n + 3 [odd] -> state copied.

*)
  
(* TODO: add assumption that on even cycle, our choice is NOTHING *)
Lemma system38_polled_if_hungy_then_eat:
  forall (n: nat)
         (NODD: odd (S n) = true)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SSSN: ValidTrace system38 ss ts (S (S (S n))))
         (BOTTOM_EVEN: forall (i: nat) (IEVEN: even i = true), snd (fst (ts i)) = nothing choice)
         (NOT_BOTTOM_ODD: forall (i: nat) (IODD: odd i = true),  snd(fst (ts i)) <> nothing choice)
         (HUNGRY: fst (ss (S n)) = h),
    fst (ss (S (S (S n)))) = e.
Proof.
  intros.
  assert (PREV_STATE_H: fst (ss n) = h).
  erewrite system38_phil_odd_state_prev_state; eauto.
  inversion TRACE_SSSN. inversion TILLN. auto.

  assert (CUR_CMD_BANG1: snd (ss (S n)) = cmd_bang1).
  eapply system38_phil_hungry_then_next_controller_bang1; eauto.
  inversion TRACE_SSSN; inversion TILLN;  eauto.

  
  assert (NEXT_STATE: fst (ss (S (S n))) = trans37fn  (fst (ss (S n))) (fst (ts (S n)))).
  eapply system38_odd_state_next_phil_state; eauto.  inversion TRACE_SSSN; auto.
  
  assert (NEXT_NEXT_STATE_EQ_NEXT_STATE: fst (ss (S (S (S n)))) = fst (ss (S (S n))) ).
  eapply system38_phil_even_state_next_state; eauto.
  apply odd_n_even_Sn; auto.

  assert (CHOICE_NEXT: snd (fst (ts (S n))) <> nothing choice).
  apply NOT_BOTTOM_ODD. apply NODD.
  
  rewrite NEXT_NEXT_STATE_EQ_NEXT_STATE.
  rewrite NEXT_STATE.
  unfold trans37fn.
  erewrite system38_s_cmd_to_t_cmd with (ss := ss); auto.
  rewrite CUR_CMD_BANG1.
  rewrite HUNGRY.
  destruct (snd (fst (ts (S n)))); auto; try contradiction.
  inversion TRACE_SSSN; auto.
Qed.

(* HELPER: reason about previous trace *)
Lemma ValidTrace_valid_pred:
  forall {X U: Set} (s: system X U) (ss: nat -> X) (ts: nat -> U)
         (n: nat) (VALID: ValidTrace s ss ts (S n)),
    ValidTrace s ss ts n.
Proof.
  intros.
  inversion VALID; auto.
Qed.


    



(* TODO: add assumption that on even cycle, our choice is NOTHING *)
Lemma system38_starvation_free:
  forall (n: nat)
         (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE_SSSN: ValidTrace system38 ss ts (S (S (S n))))
         (BOTTOM_EVEN: forall (i: nat) (IEVEN: even i = true), snd (fst (ts i)) = nothing choice)
         (NOT_BOTTOM_ODD: forall (i: nat) (IODD: odd i = true),  snd(fst (ts i)) <> nothing choice)
         (HUNGRY: fst (ss n) = h),
    exists (m: nat),  m > n /\  fst (ss m) = e.
Proof.
  intros.
  assert(N_EVEN_OR_N_ODD: even n = true \/ odd n = true).
  rewrite  <- Bool.orb_true_iff.
  apply Nat.orb_even_odd.

  destruct N_EVEN_OR_N_ODD as [N_EVEN | N_ODD].

  - assert(NEXT_STATE_HUNGRY: fst (ss (S n)) = h).
    erewrite system38_phil_even_state_next_state; eauto.
    repeat (apply ValidTrace_valid_pred; try auto).
      
    assert (SN_ODD: odd (S n) = true).
    eapply even_n_odd_Sn; auto.

    assert(NEXT_NEXT_STATE_EATING: fst (ss (S (S (S n)))) = e).
    eapply system38_polled_if_hungy_then_eat; eauto.

    exists (S (S (S n))).
    split; try omega; auto.

  - (* odd *)
    assert (N_NOT_FIRST_STATE: exists npred,  n = S npred).
    destruct n. cut (odd 0 = false). intros. congruence. apply Nat.odd_0.
    eauto.

    destruct N_NOT_FIRST_STATE as [npred NPRED].

    assert(NEXT_STATE_EATING: fst (ss (S (S n))) = e).
    rewrite NPRED.
    eapply system38_polled_if_hungy_then_eat; eauto.
    rewrite <- NPRED.
    apply ValidTrace_valid_pred.
    eapply TRACE_SSSN.
    congruence.

    exists (S (S n)); split; try omega; auto.
Qed.
