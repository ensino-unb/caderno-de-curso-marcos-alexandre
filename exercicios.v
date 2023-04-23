Section aula2.
  Variables p q r t: Prop.

    Lemma exercicio1: (p -> p -> q) -> p -> q.
    Proof.
      intro H1. intro H2. apply H1. apply H2. apply H2.
    Qed.

    Lemma exercicio2: (p -> q) -> (p -> p -> q).
    Proof.
      intro H1. intro H2. apply H1.
    Qed.

    Lemma exercicio3: (q -> r -> t) -> (p -> q) -> p -> r -> t.
    Proof.
      intro H1. intro H2. intro H3. apply H1. apply H2. apply H3.
    Qed.

    Lemma exercicio4: (p -> q -> r) -> (p -> q) -> p -> r.
    Proof.
      intro H1. intro H2. intro H3.
      apply H1. apply H3. apply H2. apply H3. (*no coq, o uso de H1 já aplica mais 
                                                eliminações e axiomas diretamente*)
    Qed.

    Lemma exercicio5: (p -> q -> r) -> (q -> p -> r).
    Proof.
      intro H1. intro H2. intro H3.
      apply H1. apply H3. apply H2. (*no coq, o uso de H1 já aplica mais 
                                     eliminações e axiomas diretamente*)
    Qed.

End aula2.
