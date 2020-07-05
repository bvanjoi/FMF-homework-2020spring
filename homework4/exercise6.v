Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise6:
  (exists x: A, (~P x \/ Q x)) ->  (exists x:A, ~(P x /\ ~Q x)).
Proof.
  intros.
  destruct H as [a  p].
  exists a.
  unfold not.
  intros.
  inversion p.
  inversion H.
  apply H0.
  apply H1.
  inversion H.
  apply H2 in H0.
  apply H0.
Qed.