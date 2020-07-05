Theorem challenge1: forall P Q R S T:Prop,
 ((P/\Q)/\R) /\ (S/\T) -> (Q /\ S).
Proof.
  intros.
  split.
  apply H.
  apply H.
Qed.