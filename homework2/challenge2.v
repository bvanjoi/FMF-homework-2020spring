Theorem challenge2: forall P Q:Prop,
 (P -> Q) -> ( ~Q -> ~P).
Proof.
  intros.
  unfold not.
  unfold not in H0.
  auto.
Qed.