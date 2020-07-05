Theorem Exercise3: forall P Q: Prop,
  P/\Q ->P.
Proof.
  intros.
  inversion H.
  apply H0.
Qed.