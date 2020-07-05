Variables A: Set.
Variables P Q R: A -> Prop.
Theorem Exercise12:
(exists x: A, P x /\ Q x) /\ (forall x:A, P x -> R x) -> exists x:A, R x /\ Q x.
Proof.
  intros.
  destruct H.
  destruct H as [a p].
  exists a.
  destruct p.
  split.
  apply H0 in H.
  apply H.
  apply H1.
Qed.