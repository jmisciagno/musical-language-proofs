Section Sets.
  Definition intersection {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
    fun r s x => r x /\ s x.
  
  Definition union {A} : (A -> Prop) -> (A -> Prop) -> (A -> Prop) :=
    fun r s x => r x \/ s x.

  Definition subset {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
    fun r s => forall x, r x -> s x.

  Definition superset {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
    fun r s => forall x, s x -> r x.
  
  Definition equal {A} : (A -> Prop) -> (A -> Prop) -> Prop :=
    fun r s => superset r s /\ superset s r.
End Sets.

Section A.
  Variables Statement Concept : Type.
  Variable eval : Statement -> Concept -> Prop.

  Definition a : (Statement -> Prop) -> (Concept -> Prop) -> Prop :=
    fun s t => forall (x : Statement), s x -> superset (eval x) t.

  Theorem P1 :
    forall (s t : Statement -> Prop),
      superset (a (union s t)) (intersection (a s) (a t)).
      firstorder.
    Defined.

  Theorem P2 :
    forall (s t : Statement -> Prop),
      superset (a (intersection s t)) (union (a s) (a t)).
    firstorder.
  Defined.

  Theorem P3 :
    forall (s t : Statement -> Prop),
      superset (intersection (a s) (a t)) (a (union s t)).
    firstorder.
  Defined.
  
  Theorem P4 :
    forall (s t : Statement -> Prop),
      superset (union (a s) (a t)) (a (union s t)).
    firstorder.
  Defined.

  Theorem P5 :
    forall (s t : Statement -> Prop),
    equal (a (union s t)) (intersection (a s) (a t)).
    firstorder.
  Defined.
End A.

Section Raise.
  Definition raise {A B} : (A -> B -> Prop) -> (A -> Prop) -> (B -> Prop) -> Prop :=
    fun r s t => forall (x : A), s x -> superset (r x) t.

    Theorem P1' {A B} :
    forall (r : A -> B -> Prop) (s t : A -> Prop),
      superset (raise r (union s t)) (intersection (raise r s) (raise r t)).
      firstorder.
    Defined.

    Theorem P2' {A B} :
      forall (r : A -> B -> Prop) (s t : A -> Prop),
        superset (raise r (intersection s t)) (union (raise r s) (raise r t)).
      firstorder.
    Defined.

    Theorem P3' {A B} :
      forall (r : A -> B -> Prop) (s t : A -> Prop),
        superset (intersection (raise r s) (raise r t)) (raise r (union s t)).
      firstorder.
    Defined.

    Theorem P4' {A B} :
      forall (r : A -> B -> Prop) (s t : A -> Prop),
        superset (union (raise r s) (raise r t)) (raise r (union s t)).
      firstorder.
    Defined.
End Raise.
