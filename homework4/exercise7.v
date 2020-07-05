Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise7:
  (exists x: A, (~P x /\ ~Q x)) ->  (exists x:A, ~(P x /\ Q x)).
Proof.
  intros.
  destruct H as [a  p].
  exists a.
  unfold not.
  intros.
  inversion p.
  inversion H.
  apply H0.
  apply H2.
Qed.