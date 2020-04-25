Require Import Nat.
Require Import List.
Require Import Omega.

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
Definition trans37fn (s: the) (u: cmd * maybe choice): the :=
  match u with
  | (_, nothing _) => s (* this looks fishy! what if I send !0 / !1? I don't trust this :(. Indeed, moving this down 
                           to be below cmd_bang0, cmd_bang1 breaks things *)
  | (cmd_bang0, _) => s
  | (cmd_bang1, _) => next s
  | (cmd_pass, just _ ch) => trans32fn s ch

  end.

Definition trans37fn' (s: the) (u: cmd * maybe choice): the :=
  match snd u   with
  | nothing _ => s (* this looks fishy! what if I send !0 / !1? I don't trust this :(. Indeed, moving this down 
                           to be below cmd_bang0, cmd_bang1 breaks things *)
  | just _ ch  => match fst u with
         | cmd_bang0 => s
         | cmd_bang1 => s
         | cmd_pass => trans32fn s ch
                  end
  end.

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
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step5: ValidTrace system38 states_table_3 trans_table_3 5.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step6: ValidTrace system38 states_table_3 trans_table_3 6.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

(* elided 7, 8 *)
Example valid_trace_table3_step9: ValidTrace system38 states_table_3 trans_table_3 9.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

Example valid_trace_table3_step10: ValidTrace system38 states_table_3 trans_table_3 10.
Proof. repeat (try constructor; simpl; try apply valid_trace_system35_step1; try apply tabuada_start). Qed.

(* do I really want to do this to myself? :( *)
(* 3.10: polled dyanmics *)
(* Definition odd_polled {A: Type} (f: nat -> A) (n: nat) := f (n * 2 + 1). *)
Definition time_to_odd_time (n: nat): nat := 2 * n + 1.


(* 3.11: correctness *)
Lemma system38_polled_if_hungy_then_eat:
  forall (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE: ValidTrace system38 ss ts 3)
         (HUNGRY: fst (ss 1) = h),
    fst (ss 3) = e.
Proof.
  intros.
  inversion TRACE.
  inversion TILLN.
  simpl in *.
  unfold tabuada_trans in *.
  destruct ATN0 as [P1 [Q1 R1]].
  destruct ATN as [P2 [Q2 R2]].
  subst.
  rewrite <- P2.
  unfold trans37fn.
  inversion R2.
  simpl.

  xx
  
  
  
  
 
(* 3.11 : correctness *)
Lemma system38_polled_if_hungy_then_eat:
  forall (ss: nat -> the * cmd)
         (ts: nat -> cmd * maybe choice * the)
         (TRACE: ValidTrace system38 ss ts 3)
         (HUNGRY: fst (ss 1) = h),
    fst (ss 3) = e.
Proof.
  intros.
  inversion TRACE as [TRACE0 | npred TRACE_PRED].
  subst.
  inversion TRACE_PRED as [TRACE0 | npredpred TRACE_PRED_PRED].
  subst.
  unfold trans in ATN, ATN0.
  unfold system38 in ATN, ATN0.
  unfold tabuada in ATN, ATN0.
  unfold tabuada_trans in ATN, ATN0.
  (* destruct ATN0 as [TRANS_PHIL_1 [TRANS_CONTROLLER_1 TRANS_CONNECT_1]].
  simpl in *. 
  inversion TRANS_CONNECT_1; subst.
  *)
  set (s2 := ss 2) in *. set (t2 := ts 2) in *.
  destruct s2; subst. destruct t2; subst.
  simpl in *.
  destruct ATN as [TRANS_PHIL_2 [TRANS_CONTROLLER_2 TRANS_CONNECT_2]].
  unfold trans in TRANS_PHIL_2.
  unfold phil37 in TRANS_PHIL_2.
  (* OK, we got the goal in a useful shape *)
  rewrite <- TRANS_PHIL_2.
  (* we now need t0, p *)
  unfold trans37fn.
  inversion TRANS_CONNECT_2;subst.
  (* now we need c *)
  destruct ATN0 as [TRANS_PHIL_1 [TRANS_CONTROLLER_1 TRANS_CONNECT_1]].
  rewrite <- TRANS_CONTROLLER_1.
  unfold trans34fn.
  (* now we need (ts 1) *)
  inversion TRANS_CONNECT_1; subst; simpl in *.
  set (s1 := ss 1) in *. destruct s1; simpl in *; inversion H0; subst.
  set (t1 := ts 1) in *. destruct t1; simpl in *; inversion H; subst.
  destruct mch; simpl in *.



  
  
    
   

Abort.
  





  


Theorem starvation_free: forall (sys: system) (n: nat), exists (m: nat) (MGTN: m > n) (hungry_at_n: state_phil sys n = hungry),
      state_phil sys m = eating.
Proof. Admitted.

