Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise9:
(exists x: A, ~P x ) -> ~(forall x:A, P x).
Proof.
  intros.
  destruct H as [a  p].
  unfold not.
  intros.
  apply p in H.
  apply H.
Qed.