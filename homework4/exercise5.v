Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise5:
  (forall x: A, (P x /\ Q x)) <-> (forall x: A, P x) /\ (forall x:A, Q x).
Proof.
  split.
  intros.
  split.
  apply H.
  apply H.
  intros.
  inversion H.
  split.
  apply H0.
  apply H1.
Qed.