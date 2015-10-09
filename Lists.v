Require Export Induction.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).
(* ===> 3 *)

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(** Exercise: 1 star (snd_fst_is_swap)  *)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p as [n m]. simpl. reflexivity.
Qed.

(** ☐
Exercise: 1 star, optional (fst_swap_is_snd)  
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.  *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Notation "x + y" := (plus x y)  
                    (at level 50, left associativity). 

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil 
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
  | true => h :: oddmembers t
  | false => oddmembers t
  end
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => 0
  | h :: t => match oddb h with
  | true => 1 + (countoddmembers t)
  | false => (countoddmembers t)
  end
  end.

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => match beq_nat v h with
  | true => 1 + (count v t)
  | false => (count v t)
  end
  end.


Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat (count v s) 0).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(** Exercise: 3 stars (bag_theorem)  *)
Fixpoint total (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => h + (total t)
  end.

Example test_total1: total [1;2;3;4;5] = 15.
Proof. reflexivity. Qed.
Example test_total2: total [ ] = 0.
Proof. reflexivity. Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    (* This is the tricky case.  Let's begin as usual 
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality 
       involving snoc, but we don't have any equations 
       in either the immediate context or the global 
       environment that have anything to do with snoc! 

       We can make a little progress by using the IH to 
       rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc.
    rewrite -> IHl'. reflexivity. Qed.

(* SearchAbout rev. *)

(** Exercise: 3 stars (list_exercises)
More practice with lists.  *)

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| l'].
  Case "l = nil". reflexivity.
  Case "l = cons". simpl. rewrite -> IHl. reflexivity.
Qed.

Lemma reverse : forall n : nat, forall l : natlist,
  rev (snoc l n) = n :: rev l.
Proof.
  intros. induction l as [| n' l'].
  Case "l = nil". simpl. reflexivity.
  Case "l = cons". simpl. rewrite -> IHl'. simpl. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| l'].
  Case "l = nil". reflexivity.
  Case "l = cons". simpl. rewrite -> reverse. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros. rewrite -> app_assoc. rewrite -> app_assoc. reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros. induction l as [| l'].
  Case "l = nil". simpl. reflexivity.
  Case "l = cons". simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros. induction l1 as [| l1'].
  Case "l1 = nil". simpl. rewrite -> app_nil_end. reflexivity.
  Case "l1 = cons". simpl. rewrite -> snoc_append. rewrite -> IHl1. 
  rewrite -> snoc_append. rewrite -> app_assoc. reflexivity.
Qed.
 
(** An exercise about your implementation of nonzeros:  *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros. induction l1 as [| l2' l1'].
  Case "l1 = nil". simpl. reflexivity.
  Case "l1 = cons".
    induction l2' as [| l2'']. 
    SCase "L2 = nil". simpl. rewrite -> IHl1'. reflexivity.
    SCase "L2 = cons". simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with 
  | nil, nil => true
  | _, nil => false
  | nil, _ => false
  | h :: t, h' :: t' => andb (beq_nat h h') (beq_natlist t t') 
  end.


Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros. induction l as [| l'].
  Case "l = nil". simpl. reflexivity.
  Case "l = cons". simpl. rewrite -> IHl. admit.
Qed.

(** Exercise: 2 stars (list_design)  *)

SearchAbout cons.
SearchAbout snoc.
SearchAbout app.

(** Theorem cons_snoc_app :  *)

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42 (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => index_bad (pred n) l'
               end
  end.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => index (pred n) l'
               end
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4;5;6;7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4;5;6;7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end. 

Definition hd_opt (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

Fixpoint find (key : nat) (d : dictionary) : natoption :=
  match d with
  | empty => None
  | record k v d' => if (beq_nat key k)
                       then (Some v)
                       else (find key d')
  end.

Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros. simpl. admit.
Qed.

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
  intros. simpl. rewrite -> H. reflexivity. 
Qed.

End Dictionary.

End NatList.