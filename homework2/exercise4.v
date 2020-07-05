Theorem exercise4: forall P Q R:Prop,
  (P /\ (Q /\ R)) -> ( (P /\ Q) /\ R).
Proof.
  intros.
  inversion H.
  split.
  split.
  apply H0.
  apply H1.
  apply H.
Qed.