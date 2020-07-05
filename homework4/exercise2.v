Theorem exercise2: forall P Q R: Prop,
  P /\ (Q\/R) <-> (P/\Q) \/ (P/\R).
Proof.
  split.
  intros.
  destruct H as [H1 H2].
  inversion H2.
  left.
  split.
  apply H1.
  apply H.
  right.
  split.
  apply H1.
  apply H.
  intros.
  inversion H.
  split.
  inversion H0.
  apply H1.
  inversion H0.
  left.
  apply H2.
  split.
  inversion H0.
  apply H1.
  inversion H0.
  right.
  apply H2.
Qed.
  