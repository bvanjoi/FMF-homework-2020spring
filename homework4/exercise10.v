Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise10:
(forall x: A, P x -> ~Q x) -> ~(exists x:A, (P x /\ Q x)).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0 as [a  p].
  destruct p as [p1 p2].
  apply H in p2.
  apply p2.
  apply p1.
Qed.