Variables Statement Concept : Type.
Variable eval : Statement -> Concept -> Prop.
Definition Language : Type := Statement -> Prop.

Definition subset {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
  fun r s => forall x, r x -> s x.

Definition superset {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
  fun r s => forall x, s x -> r x.

Definition equal {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
  fun r s => superset r s /\ superset s r.

Definition intersection {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
  fun r s x => r x /\ s x.

Definition union {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
  fun r s x => r x \/ s x.

Definition interpret : Language -> (Concept -> Prop) -> Prop :=
  fun (L : Statement -> Prop) (X : Concept -> Prop) =>
    forall (s : Statement),
      L s -> subset (eval s) X.

Theorem P1 :
  forall (L1 L2 : Language),
    superset (interpret (union L1 L2)) (intersection (interpret L1) (interpret L2)).
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

Theorem P2 : forall (L1 L2 : Language),
    superset (interpret (intersection L1 L2)) (union (interpret L1) (interpret L2)).
  intros.
  compute.
  intros.
  inversion H0.
  inversion H.
  apply (H4 s H2 x0 H1).
  apply (H4 s H3 x0 H1).
Defined.

Theorem P3 :
  forall (L1 L2 : Language),
    superset (intersection (interpret L1) (interpret L2)) (interpret (union L1 L2)).
  intros.
  compute.
  intros.
  split.
  intros.
  apply (H s (or_introl H0) x0 H1).
  intros.
  apply (H s (or_intror H0) x0 H1).
Defined.

Theorem P4 :
  forall (L1 L2 : Language),
    superset (union (interpret L1) (interpret L2)) (interpret (union L1 L2)).
  intros.
  compute.
  intros.
  left.
  intros.
  apply (H s).
  left.
  apply H0.
  apply H1.
Defined.

Theorem P5 :
  forall (L1 L2 : Language),
    equal (interpret (union L1 L2)) (intersection (interpret L1) (interpret L2)).
  unfold equal.
  split.
  apply (P1 L1 L2).
  apply (P3 L1 L2).
Defined.
