Theorem exercise1: forall P Q:Prop,
~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros.
  split.
  intros.
  apply H.
  left.
  apply H0.
  intros.
  apply H.
  right.
  apply H0.
Qed.