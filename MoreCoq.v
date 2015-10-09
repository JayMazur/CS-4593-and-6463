Require Export Poly.
Require Export Lists.

(** The apply Tactic  *)

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with 
     "rewrite → eq2. reflexivity." as we have 
     done several times above. But we can achieve the
     same effect in a single step by using the 
     apply tactic instead: *)
  apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall(q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall(n m : nat),
     (n,n) = (m,m) ->
     (forall(q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly3_firsttry : forall(n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use apply directly *)
Abort.


Theorem silly3 : forall(n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this simpl is unnecessary, since 
            apply will perform simplification first. *)
  apply H. Qed.

(** Exercise: 3 stars (apply_exercise1)
    Hint: you can use apply with previously defined lemmas, 
    not just hypotheses in the context. Remember that 
    SearchAbout is your friend.  *)

Lemma reverse : forall n : nat, forall (l : list nat),
  rev (snoc l n) = n :: rev l.
Proof.
  intros. induction l as [| n' l'].
  Case "l = nil". simpl. reflexivity.
  Case "l = cons". simpl. rewrite -> IHl'. simpl. reflexivity.
Qed.

Theorem rev_involutive : forall (l : list nat),
  rev (rev l) = l.
Proof.
  intros l. induction l as [| l'].
  Case "l = nil". reflexivity.
  Case "l = cons". simpl. rewrite -> reverse. rewrite -> IHl. reflexivity.
Qed.

Theorem rev_exercise1 : forall(l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros. symmetry. rewrite -> H. apply rev_involutive.
Qed.

(** The apply ... with ... Tactic  *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* If we simply tell Coq apply trans_eq at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate X
     with [nat], n with [a,b], and o with [e,f].
     However, the matching process doesn't determine an
     instantiation for m: we have to supply one explicitly
     by adding with (m:=[c,d]) to the invocation of
     apply. *)
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2. Qed.

(** The inversion tactic  *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly4 : forall(n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity. Qed.

Theorem silly5 : forall(n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** Exercise: 1 star (sillyex1)  *)
Example sillyex1 : forall(X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros. inversion H. inversion H0. inversion H2. reflexivity.
Qed.

Theorem silly6 : forall(n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall(n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

(** Exercise: 1 star (sillyex2)  *)
Example sillyex2 : forall(X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros. inversion H. Qed.

Theorem f_equal : forall(A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

(** Using Tactics on Hypotheses  *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem S_inj : forall(n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall(n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

(** Exercise: 3 stars (plus_n_n_injective)
    Practice using "in" variants in this exercise.  *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
  Case "n = 0". intros. destruct m as [| m'].
  SCase "m = 0". reflexivity.
  SCase "m = S m'". inversion H.
  Case "n = S n'". intros. destruct m as [| m'].
  SCase "m = 0". inversion H. 
  SCase "S m'". inversion H. rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H.
  inversion H. apply IHn' in H2. rewrite -> H2. reflexivity.
Qed.

(** Varying the Induction Hypothesis  *)

(** Theorem double_injective: forall n m, double n = double m -> n = m. 
  intros n. induction n.  *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'". apply f_equal.
      (* Here we are stuck.  The induction hypothesis, IHn', does
         not give us n' = m' -- there is an extra S in the
         way -- so the goal is not provable. *)
      Abort.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ m), but the IH is
       correspondingly more flexible, allowing us to
       choose any m we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular m and introduce the
       assumption that double n = double m.  Since we
       are doing a case analysis on n, we need a case
       analysis on m to keep the two "in sync." *)
    destruct m as [| m'].
    SCase "m = O".
      (* The 0 case is trivial *)
      inversion eq.
    SCase "m = S m'".
      apply f_equal.
      (* At this point, since we are in the second
         branch of the destruct m, the m' mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the S branch of
         the induction, this is perfect: if we
         instantiate the generic m in the IH with the
         m' that we are talking about right now (this
         instantiation is performed automatically by
         apply), then IHn' gives us exactly what we
         need to finish the proof. *)
      apply IHn'. inversion eq. reflexivity. Qed.

(** Exercise: 2 stars (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". intros. destruct m as [| m'].
  SCase "m = 0". reflexivity.
  SCase "m = S m'". simpl in H. inversion H.
  Case "n = S n'". intros m H. destruct m as [| m'].
  SCase "m = 0". inversion H.
  SCase "m = S m'". apply f_equal. apply IHn'. apply H.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].

  Case "l = []".
    intros n eq. rewrite <- eq. reflexivity.

  Case "l = v' :: l'".
    intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.

(** Exercise: 3 stars (gen_dep_practice)
Prove this by induction on l.  *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros n X l. generalize dependent n. induction l as [| l'].
  Case "l = nil". simpl. reflexivity.
  Case "l = cons". intros n H. simpl. destruct n as [| n'].
  SCase "n = 0". simpl. inversion H.
  SCase "n = S n'". simpl. apply IHl. simpl in H. inversion H. reflexivity.
Qed.

(** Using destruct on Compound Expressions  *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity. Qed.

(** Exercise: 1 star (override_shadow)  *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros. unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true".  admit.
  Case "beq_nat k1 k2 = false". admit.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got stuck
    above, except that the context contains an extra equality
    assumption, which is exactly what we need to make progress. *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* When we come to the second equality test in the body of the
       function we are reasoning about, we can use eqn: again in the
       same way, allow us to finish the proof. *)
      destruct (beq_nat n 5) eqn:Heqe5.
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq. Qed.

(** Exercise: 2 stars (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct b.
  Case "b = true". destruct (f true) eqn:hold.
  SCase "hold = true". rewrite hold. rewrite hold. reflexivity.
  SCase "hold = false". destruct (f false) eqn:hold2.
  SSCase "hold2 = true". apply hold.
  SSCase "hold2 = false". apply hold2.
  Case "b = false". destruct (f false) eqn:holdf.
  SCase "holdf = true". destruct (f true) eqn:holdf2.
  SSCase "holdf2 = true". apply holdf2.
  SSCase "holdf2 = false". apply holdf.
  SCase "holdf = false". rewrite holdf. apply holdf.
Qed.

(** Exercise: 2 stars (override_same)  *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros. unfold override. destruct (beq_nat k1 k2) eqn:hold.
  Case "true". admit. admit.
Qed.

(** Exercise: 3 stars (beq_nat_sym)  *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros. generalize dependent m. induction n as [| n'].
  Case "n = 0". destruct m as [| m'].
  SCase "m = 0". reflexivity.
  SCase "m = S m". destruct m' as [| m''].
  SSCase "m' = 0". reflexivity.
  SSCase "m' = S m'". reflexivity.
  Case "n = S n'". destruct m as [| m'].
  SCase "m = 0". reflexivity. simpl. rewrite IHn'. reflexivity.
Qed.

(** Exercise: 3 stars (override_permute)  *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros. destruct (beq_nat k1 k3) eqn:hold.
  Case "(beq_nat k1 k3) = true". destruct (beq_nat k2 k3) eqn:hold2.
  SCase "(beq_nat k2 k3) = true". apply beq_nat_true in hold. rewrite hold in H. rewrite hold2 in H. inversion H.
  SCase "(beq_nat k2 k3) = false". unfold override. admit. admit. Qed.