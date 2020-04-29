Inductive X: Set := X1 | X2 | X3.
Inductive Y: Set := Y1 | Y2 | Y3. 

Definition x2y_fn (x: X): Y :=
  match x with
  | X1 => Y1 | X2 => Y2 | X3 => Y3 end.

Definition x2y_rel (x: X) (y: Y): Prop :=
  (x = X1 /\ y = Y1) \/ (x = X2 /\ y = Y2) \/  (x = X3 /\ y = Y3).

Lemma x1_to_y1_fn: x2y_fn X1 = Y1. Proof. reflexivity. Qed.
Lemma x1_to_y2_rel: x2y_rel X1 Y1.
Proof.
  try reflexivity. (* Does not work! Not computational *)
  unfold x2y_rel. left. auto.
Qed.









