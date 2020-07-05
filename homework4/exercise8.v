Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise8:
(exists x: A, (P x \/ Q x)) <-> (exists x:A, P x) \/ (exists x:A, Q x).
Proof.
  split.
  intros.
  destruct H as [a  p].
  inversion p.
  left.
  exists a.
  apply H.
  right.
  exists a.
  apply H.
  intros.
  inversion H.
  destruct H0 as [a p].
  exists a.
  left.
  apply p.
  destruct H0 as [a p].
  exists a.
  right.
  apply p.
Qed.