
Require Import List.


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

Inductive choice := stay | switch.
Definition trans32fn (s: the) (c: choice): the :=
  match c with
  | stay => s | switch => next s
  end.
Definition isthinking (s: the): Prop := s = t.
Definition phil32 := mksystem the choice  isthinking  (fun s u s' => trans32fn s u = s').

(* Problems: Proposition 3.1 (end of page 15). B \omega ( Q ) = B \omega ( P ) . 
   - The set B w has not been defined before. Indeed, this statement is meaningless on its own
     without guessing.
   - 
*)

(* 3.3 Interfacing control *)
Inductive cmd := pass | bang0 | bang1.
(* composition *)
Definition trans33fn (s: the) (u: cmd * choice): the :=
  match u with
  | (pass, ch) => trans32fn s ch
  | (bang0, _) => s
  | (bang1, _) => next s
  end.

Definition phil33 := mksystem the (cmd * choice) isthinking  (fun s u s' => trans33fn s u = s').

(* 3.4 Controller *)
Definition ispass (c: cmd):Prop := c = pass.
Definition trans34fn (s: cmd) (u: the): cmd :=
  match u with
  | h => bang1 | e => pass | t => pass
  end.
Definition controller34 := mksystem cmd the ispass (fun s u s' => trans34fn s u = s').

(* feedback composition: we shall define tabuada composition here *)
Check (phil33).
Inductive connect34: the * cmd ->
                     (cmd * choice) * the -> Prop :=
  | mkconnect34: forall (sx: the) (sy: cmd) (ch: choice), connect34 (sx, sy) ((sy, ch), sx).

(* This will do the wrong thing, since it will connect my *current state* with the *transition action*?
   but the transition action is attempting to dictate my *next state* *)
Definition system35 := tabuada phil33 controller34 connect34.


(* relation is checked upto: [0-1, 1-2, ...(n-1)-n] *)
(* states, choices *)
Inductive ValidTrace {X U: Type} (trans: X -> U -> X -> Prop): (nat -> X) -> (nat -> U) -> nat -> Prop :=
| Start: forall (xs: nat -> X) (us: nat -> U), ValidTrace trans xs us  0
| Cons: forall (xs: nat -> X) (us: nat -> U) (n: nat) (TILLN: ValidTrace trans xs us  n) (ATN: trans (xs n) (us n) (xs (S n))),
    ValidTrace trans xs us (S n).


Theorem starvation_free: forall (sys: system) (n: nat), exists (m: nat) (MGTN: m > n) (hungry_at_n: state_phil sys n = hungry),
      state_phil sys m = eating.
Proof. Admitted.
