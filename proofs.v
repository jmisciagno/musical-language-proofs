Definition intersection {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
  fun r s x => r x /\ s x.

Definition union {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
  fun r s x => r x \/ s x.

Definition subset {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
  fun r s => forall x, s x -> r x.

Definition equal {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
  fun r s => subset r s /\ subset s r.

Variables Statement Affect : Type.
Definition Language : Type := Statement -> Prop.
Definition Emotion : Type := Affect -> Prop.
Variable eval : Statement -> Emotion.

Definition interpret : Language -> Emotion -> Prop :=
  fun (L : Statement -> Prop) (E : Affect -> Prop) =>
    forall (s : Statement),
      L s -> subset (eval s) E.

Theorem X : forall (L1 L2 : Language)
                   (E1 E2 : Emotion),
    interpret L1 E1 -> interpret L2 E2 -> interpret (intersection L1 L2) (union E1 E2).
  compute.
  intros.
  pose (H s) as H3.
  pose (H0 s) as H4.
  inversion H1.
  pose (H3 H5 x) as H7.
  pose (H4 H6 x) as H8.
  inversion H2.
  apply (H7 H9).
  apply (H8 H9).
Defined.

Theorem Y : forall (L1 L2 : Language)
                   (E1 E2 : Emotion),
    interpret L1 E1 -> interpret L2 E2 -> interpret (union L1 L2) (intersection E1 E2).
  compute.
  intros.
  pose (H s) as H3.
  pose (H0 s) as H4.
  inversion H1.
  pose (H3 H5 x) as H6.
  inversion H2.
  apply (H6 H7).
  pose (H4 H5 x) as H6.
  inversion H2.
  apply (H6 H8).
Defined.

Theorem Z : forall (L1 L2 : Language),
    equal (interpret (union L1 L2)) (intersection (interpret L1) (interpret L2)).
  intros.
  unfold equal.
  split.
  compute.
  intros.
  inversion H.
  pose (H2 s) as H4.
  pose (H3 s) as H5.
  inversion H0.
  apply (H4 H6).
  apply H1.
  apply (H5 H6).
  apply H1.
  compute.
  intros.
  split.
  intro.
  pose (H s) as H0.
  intros.
  pose (H0 (or_introl H1)) as H3.
  apply (H3 x0 H2).
  intros.
  pose (H s) as H2.
  pose (H2 (or_intror H0)) as H3.
  apply (H3 x0 H1).
Defined.

Theorem Z2 : forall (L1 L2 : Language),
    subset (interpret (union L1 L2)) (intersection (interpret L1) (interpret L2)).
  intros.
  compute.
  intros.
  inversion H.
  inversion H0.
  apply (H2 s H4).
  apply H1.
  apply (H3 s H4).
  apply H1.
Defined.
