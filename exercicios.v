Section aula2.
  Variables p q r: Prop.
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

End aula2.
