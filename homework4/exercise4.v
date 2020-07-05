Variables A: Set.
Variables P Q: A -> Prop.
Theorem Exercise4:
  (forall x: A, (P x -> Q x)) -> (forall x: A,~Q x) -> (forall x: A, ~P x).
Proof.
  intros.
  intros H1.
  apply H in H1.
  apply H0 in H1.
  apply H1.
Qed.