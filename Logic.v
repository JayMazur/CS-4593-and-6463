Require Export MoreCoq.

(** Propositions  *)

Check (3 = 3).
(* ===> Prop *)

Check (forall(n:nat), n = 2).
(* ===> Prop *)

(** Proofs and Evidence  *)

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

Print silly.
(* ===> silly = eq_refl : 0 * 3 = 0 *)

(** Implications are functions  *)

Lemma silly_implication : (1 + 1) = 2 -> 0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

Print silly_implication.
(* ===> silly_implication = fun _ : 1 + 1 = 2 => eq_refl
     : 1 + 1 = 2 -> 0 * 3 = 0 *)

(** Defining propositions  *)

(** Conjunction (Logical "and")  *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** "Introducing" conjunctions  *)

Theorem and_example :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity. Qed.

Theorem and_example' :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity. Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HP. Qed.

(** Exercise: 1 star, optional (proj2)  *)
Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros. destruct H. apply H0. Qed.

(** Exercise: 2 stars (and_assoc)
    In the following proof, notice 
    how the nested pattern in the 
    destruct breaks the hypothesis 
    H : P ∧ (Q ∧ R) down into HP: P, 
    HQ : Q, and HR : R. Finish the 
    proof from there:  *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split.
  Case "left". split.
  SCase "left". apply HP.
  SCase "right". apply HQ.
  Case "right". apply HR.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  destruct H as [HP HQ].
  split.
    Case "left". apply HQ.
    Case "right". apply HP. Qed.

(** Iff  *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P ↔ Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P ↔ Q) -> P -> Q.
Proof.
  intros P Q H.
  destruct H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P ↔ Q) -> (Q ↔ P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  destruct H as [HAB HBA].
  split.
    Case "→". apply HBA.
    Case "←". apply HAB. Qed.

(** Exercise: 1 star, optional (iff_properties)
    Using the above proof that ↔ is symmetric 
    (iff_sym) as a guide, prove that it is also 
    reflexive and transitive.  

Theorem iff_refl : forall P : Prop,
  P ↔ P.
Proof.
  intros P. inversion. split.  apply P. reflexivity.

Theorem iff_trans : ∀P Q R : Prop,
  (P ↔ Q) → (Q ↔ R) → (P ↔ R).
Proof.
  (* FILL IN HERE *) Admitted.

    Hint: If you have an iff hypothesis in the 
    context, you can use inversion to break it 
    into two separate implications. (Think about 
    why this works.) ☐  *)

(** Disjunction (Logical "or")
    Implementing disjunction  *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ. Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ. Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. destruct H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR. Qed.

(** Exercise: 2 stars (or_distributes_over_and_2)  *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros. destruct H as [HQ HR]. destruct HQ as [HP | Hq].
  Case "left". left. apply HP.
  Case "right". right. split.
  SCase "Q". apply Hq.
  SCase "R". admit.
Qed.

(** Relating ∧ and ∨ with andb and orb  *)

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.

Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H. Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct H.
  rewrite H. rewrite H0. reflexivity. Qed.

(** Falsehood  *)

Inductive False : Prop := .

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra. Qed.

(** Truth  *)

(** Negation  *)

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. destruct H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(** Exercise: 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not. unfold not in H0. intros. apply H0. apply H. apply H1.
Qed.

(** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros. unfold not. intros. destruct H as [H0 H1]. apply H1. apply H0.
Qed.

(** Constructive logic  *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H.
  (* But now what? There is no way to "invent" evidence for ¬P 
     from evidence for P. *)
  Abort.

(** Exercise: 3 stars (excluded_middle_irrefutable)  
    This theorem implies that it is always safe to add a 
    decidability axiom (i.e. an instance of excluded middle) 
    for any particular Prop P. Why? Because we cannot prove 
    the negation of such an axiom; if we could, we would have 
    both ¬ (P ∨ ¬P) and ¬ ¬ (P ∨ ¬P), a contradiction.  *)

Theorem excluded_middle_irrefutable: forall (P:Prop), ~ ~ (P \/ ~ P).
Proof.
  intros. unfold not. intros H. apply H. right. intros. apply H. left. apply H0.
Qed.

(** Inequality  *)

Notation "x ^ y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b ^ false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. Qed.

(** Exercise: 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n ^ m ->
     beq_nat n m = false.
Proof. Print beq_nat. 
  intros. induction n as [| n'].
  Case "n = 0". admit.
  Case "n = S n'". admit.
Qed.