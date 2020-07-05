Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise11:
(forall x: A, P x -> Q x) /\ (exists x:A, P x) -> exists x:A, Q x.
Proof.
  intros.
  destruct H.
  destruct H0 as [a p].
  exists a.
  apply H in p.
  apply p.
Qed.