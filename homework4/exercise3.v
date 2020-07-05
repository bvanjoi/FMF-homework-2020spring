Variables A B: Set.
Variables P Q: A -> Prop.
Theorem exercise3:
(forall x:A, ~P x /\ Q x) -> (forall x:A, P x -> Q x).
Proof.
  intros.
  apply H.
Qed.