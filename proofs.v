Section Sets.
  Definition intersection {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
    fun r s x => r x /\ s x.
  
  Definition union {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
    fun r s x => r x \/ s x.

  Definition superset {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
    fun r s => forall x, s x -> r x.
  
  Definition equal {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
    fun r s => superset r s /\ superset s r.
End Sets.

Section Raise.
  Definition raise {A B} : (A -> B -> Prop) -> (A -> Prop) -> (B -> Prop) -> Prop :=
    fun r s t => forall (a : A) (b : B), s a -> r a b -> t b.

  Theorem P1 {A B} :
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      superset (raise r (union s t)) (intersection (raise r s) (raise r t)).
    intros.
    compute.
    intros.
    inversion H.
    inversion H0.
    apply (H2 a b H4 H1).
    apply (H3 a b H4 H1).
  Defined.
  
  Theorem P2 {A B} :
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      superset (raise r (intersection s t)) (union (raise r s) (raise r t)).
    intros.
    compute.
    intros.
    inversion H0.
    inversion H.
    apply (H4 a b H2 H1).
    apply (H4 a b H3 H1).
  Defined.
  
  Theorem P3 {A B} :
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      superset (intersection (raise r s) (raise r t)) (raise r (union s t)).
    intros.
    compute.
    intros.
    split.
    intros.
    apply (H a b (or_introl H0) H1).
    intros.
    apply (H a b (or_intror H0) H1).
  Defined.
  
  Theorem P4 {A B} :
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      superset (union (raise r s) (raise r t)) (raise r (union s t)).
    intros.
    compute.
    intros.
    left.
    intros.
    apply (H a b (or_introl H0) H1).
  Defined.

  Theorem P4' {A B} :
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      superset (union (raise r s) (raise r t)) (raise r (union s t)).
    intros.
    compute.
    intros.
    right.
    intros.
    apply (H a b (or_intror H0) H1).
  Defined.

  Theorem P5 {A B} :
    forall (r : A -> B -> Prop) (s t: A -> Prop),
      equal (raise r (union s t)) (intersection (raise r s) (raise r t)).
    unfold equal.
    split.
    apply (P1 r s t).
    apply (P3 r s t).
  Defined.
  
  Definition P6_Type A B :=
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      superset (union (raise r s) (raise r t)) (raise r (intersection s t)).
  
  Theorem P7 {A B} :
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      (P6_Type A B) -> equal (raise r (intersection s t)) (union (raise r s) (raise r t)).
    unfold P6_Type.
    unfold equal.  
    intros.
    split.
    apply (P2 r s t).
    apply (H r s t).
  Defined.
End Raise.  

