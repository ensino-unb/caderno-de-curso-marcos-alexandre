(* begin hide *)
Require Import Arith List Recdef.
(* end hide *)

(** * Atividade: A correção do algoritmo bubblesort - 10 pontos até 16 de julho de 2023. *)     

(** O algoritmo [bubblesort] é baseado na função [bubble] que percorre a lista dada como argumento comparando seus elementos consecutivos: *)
(* printing *)
(** printing <=? $\leq ?$ *)

Function bubble (l: list nat) {measure length} :=
  match l with
  | h1 :: h2 :: tl =>
    if h1 <=? h2
    then  h1 :: (bubble (h2 :: tl))
    else h2 :: (bubble (h1 :: tl))
    | _ => l
  end.
(* begin hide *)
Proof.
  - intros. simpl.
    apply Nat.lt_succ_diag_r.
  - intros.
    simpl.
    apply Nat.lt_succ_diag_r.
Defined.
(* end hide *)

Eval compute in (bubble (3::2::1::nil)).

(** ** A função principal  *)

Fixpoint bubblesort (l: list nat) :=
  match l with
  | nil => nil
  | h :: tl => bubble (h :: bubblesort tl)
  end.

Eval compute in (bubblesort (3::2::1::nil)).

Require Import Permutation.
Print Permutation.

(* coq.inria.fr *)

(** ** Parte 1: o predicado [sorted] nos permite provar quando uma lista está ordenada: *)

Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

(** ** Parte 2 : o predicado [perm] nos permite provar quando de duas listas são permutações uma da outra: *)

Inductive perm: list nat -> list nat -> Prop :=
| perm_refl: forall l, perm l l
| perm_hd: forall x l l', perm l l' -> perm (x::l) (x::l')
| perm_swap: forall x y l l', perm l l' -> perm (x::y::l) (y::x::l')
| perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

(* opcional *)

Lemma equiv: forall l (a:nat), Permutation l l -> Permutation (a :: l) (a :: l).
  Proof.
    intros l a l'. induction l.
      - admit.
      - admit.
    Admitted.


Lemma equiv2: forall l l' (x y:nat), Permutation l l' -> Permutation (x :: y :: l) (y :: x :: l').
  Proof.
    intros l l' x y h.
    Admitted.

Lemma equiv3: forall (l1 l2 l3: list nat), Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3.
  Proof.
    intros l1 l2 l3. apply perm_trans. Print Permutation. Check perm_trans. eapply perm_trans.
    Admitted.

Theorem perm_equiv: forall l1 l2, perm l1 l2 <-> Permutation l1 l2.
Proof.
  intros l1 l2. split.
    - intro l. induction l.
      * induction l.
        + apply perm_nil. 
        + apply equiv. apply IHl.
      * apply perm_skip. apply IHl.
      * Print Permutation. apply equiv2. apply IHl.
      * apply equiv3 with l2. apply IHl1. apply IHl2.
    - intro l. induction l.
      * apply perm_refl.
      * apply perm_hd. apply IHl.
      * apply perm_swap. apply perm_refl.
      * apply perm_trans with l'.
        + apply IHl1.
        + apply IHl2.
  Admitted.
  
(** O resultado principal, que caracteriza a correção do algoritmo de ordenação [bubblesort], é  dado a seguir: *)

Lemma perm_bubble: forall l, perm (bubble l) l.
Proof.
  intro l. functional induction (bubble l).
  - apply perm_hd. apply IHl0.
  - apply perm_trans with (h2::h1::tl).
    + apply perm_hd. apply IHl0.
    + apply perm_swap. apply perm_refl.
  - apply perm_refl.
Qed.
  
Lemma perm_bubblesort: forall l, perm (bubblesort l) l.
Proof.
  induction l.
  - simpl. apply perm_refl.
  - simpl. apply perm_trans with (a::(bubblesort l)).
    + apply perm_bubble.
    + apply perm_hd. apply IHl.
Qed.

Require Import Lia.


Lemma bubble_sorted: forall l, sorted l -> bubble l = l.
  Proof.
    intro l. functional induction (bubble l).
    - intro H. inversion H; subst. apply IHl0 in H2. rewrite H2. reflexivity.
    - intro H. inversion H; subst. apply leb_correct in H4. rewrite e0 in H4. discriminate.
    - intro H. reflexivity. 
  Qed.

Require Import Lia.

Lemma sorted_bubble: forall l a, sorted l ->  sorted (bubble (a::l)).
Proof.
  intros l a H. induction H.
    - rewrite bubble_equation. apply one_sorted.
    - rewrite bubble_equation. destruct(a <=? n) eqn:H.
      *rewrite bubble_equation. apply all_sorted.
        + apply one_sorted.
        + apply leb_complete. apply H.
      * rewrite bubble_equation. apply all_sorted.
        + apply one_sorted.
        + apply Nat.leb_nle in H. lia.
    - rewrite bubble_equation. destruct (a <=? x) eqn:H'.
      * rewrite bubble_sorted.
        + apply all_sorted.
          -- apply all_sorted.
            ** apply H.
            ** apply H0.
          -- apply leb_complete. apply H'.
        + apply all_sorted.
          -- apply H.
          -- apply H0.
      * rewrite bubble_equation. destruct (a <=? y) eqn:H''.
        + apply all_sorted.
          -- rewrite bubble_sorted.
            ** apply all_sorted. 
                ++ apply H.
                ++ apply leb_complete. apply H''.
            **  apply H.
          -- apply Nat.leb_nle in H'. lia.
        + rewrite bubble_equation in IHsorted. rewrite H'' in IHsorted. apply all_sorted.
          -- apply IHsorted.
          --  apply Nat.leb_nle in H'. apply Nat.leb_nle in H''. lia.
Qed.

Lemma sorted_bubblesort: forall l, sorted (bubblesort l).
Proof.
  induction l.
  - simpl. apply nil_sorted.
  - simpl. apply sorted_bubble. apply IHl.
Qed.


Theorem bubblesort_is_correct: forall l, perm (bubblesort l) l /\ sorted (bubblesort l).
Proof.
  intro l. split.
  - apply perm_bubblesort.
  - apply sorted_bubblesort.
Qed.


(* begin hide *)

(** ** Extração de código *)


Require Extraction.

(** As opções de linguagens são: Ocaml, Haskell e Scheme. *)
Extraction Language Haskell.

(** Extração apenas da função [bubblesort]. *) Extraction bubblesort.

(** Extração do programa inteiro. *) Recursive Extraction bubblesort.

(** Extração para um arquivo. *) Extraction "bubblesort" bubblesort.

Theorem sorted_exists: forall l, exists l', perm l' l /\ sorted l'.
Proof.
  intro l. exists (bubblesort l).
  apply bubblesort_is_correct.
Qed.
  
(* end hide *)
