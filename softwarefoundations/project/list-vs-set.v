Inductive  list (A: Type): Type :=
  nil : list A | cons : A -> list A -> list A.

Lemma list_eq_equational: forall
    (X: Type)
    (x x': X) (xs xs': list X)
    (EQ: cons X x xs = cons X x' xs'),
    x = x' /\ xs = xs'.
Proof.
  intros. inversion EQ. (* equational *)
  auto.
Qed.

