Section ex88e87.

  (* Exercício 87 *)
  Lemma PIG: forall (P : nat -> Prop) (k : nat), P k ->
        (forall n, n >= k -> P n -> P (S n)) ->
          forall n : nat, n >= k -> P n.
    Proof.
      intros P k H1 IH n H2.
      assert (H := nat_ind (fun n => n >= k -> P n)).
    generalize dependent n. apply H.
      - intro H3. replace 0 with k. apply H1. inversion H3. reflexivity.
      - intros n H0 H4. inversion H4. 
          + rewrite H2 in H1. apply H1.
          + apply IH. 
             * apply H3.
             * apply H0. apply H3.
    Qed.
  
(* Exercício 88 *)
  Lemma PIM : forall P: nat -> Prop,
              (P 0) ->
              (forall n, P n -> P (S n)) ->
                forall n, P n.
    Proof.
      intros P H IH n.
      apply PIG with 0.
      - apply H.
      - intros. apply IH. apply H1.
      - induction n.
          + apply le_n.
          + apply le_S. apply IHn.
    Qed.

End ex88e87.

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
