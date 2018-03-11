Section Sets.
  Definition intersection {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
    fun r s x => r x /\ s x.
  
  Definition union {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
    fun r s x => r x \/ s x.

  Definition subset {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
    fun r s => forall x, r x -> s x.

  Definition equal {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
    fun r s => subset r s /\ subset s r.

End Sets.

Definition raise {A B} : (A -> B -> Prop) -> (A -> Prop) -> B -> Prop :=
  fun r s b => forall a, s a -> r a b.

Theorem P1 {A B} :
  forall (r : A -> B -> Prop) (s t : A -> Prop),
    subset (intersection (raise r s) (raise r t)) (raise r (union s t)) .
  compute.
  intros.
  inversion H.
  inversion H0.
  apply (H1 a H3).
  apply (H2 a H3).
Defined.

Theorem P2 {A B} :
  forall (r : A -> B -> Prop) (s t : A -> Prop),
    subset (raise r (union s t)) (intersection (raise r s) (raise r t)).
  compute.
  intros.
  split.
  intros.
  apply (H a (or_introl H0)).
  intros.
  apply (H a (or_intror H0)).
Defined.

Theorem P3 {A B} :
  forall (r : A -> B -> Prop) (s t : A -> Prop),
    subset (union (raise r s) (raise r t)) (raise r (intersection s t)) .
  compute.
  intros.
  inversion H0.
  inversion H.
  apply (H3 a H1).
  apply (H3 a H2).
Defined.

Theorem P4 {A B} :
  forall (r : A -> B -> Prop) (s t : A -> Prop),
    subset (raise r (union s t)) (union (raise r s) (raise r t)).
  compute.
  intros.
  left.
  intros.
  apply (H a (or_introl H0)).
Defined.

Theorem P5 {A B} :
  forall (r : A -> B -> Prop) (s t : A -> Prop),
    subset (intersection (raise r s) (raise r t)) (raise r (intersection s t)) .
  compute.
  intros.
  inversion H0.
  inversion H.
  apply (H3 a H1).
Defined.
  
Theorem P6 {A B} :
  forall (r : A -> B -> Prop) (s t : A -> Prop),
    equal (intersection (raise r s) (raise r t)) (raise r (union s t)) .
  unfold equal.
  intros.
  split.
  apply (P1 r s t).
  apply (P2 r s t).
Defined.
