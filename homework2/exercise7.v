Theorem exercise7: forall P Q R:Prop,
 (P->(Q/\R))-> ((P->Q)/\(P->R)).
Proof.
  intros.
  split.
  apply H.
  apply H.
Qed.