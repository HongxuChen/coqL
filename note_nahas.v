(* a note from https://coq.inria.fr/tutorial-nahas;
original coq file: https://github.com/coq/www/blob/master/files/nahas_tutorial.v *)

Theorem hw_proof : (forall A B: Prop, A->(A->B)->B).
Proof.
  intros A B A_implies_B proof_of_A.
  apply proof_of_A. assumption.
Qed.

Theorem hw_proof_more_bwd : (forall A B C: Prop, A->(A->B)->(B->C)->C).
Proof.
  intros A B C proof_of_A A_implies_B B_implies_C.
  apply B_implies_C. apply A_implies_B. assumption.
Qed.

Theorem bwd_huge : (forall A B C: Prop, A->(A->B)->(A->B->C)->C).
Proof.
  intros A B C pA A_imp_B A_imp_B_imp_C.
  apply A_imp_B_imp_C in A_imp_B. assumption. assumption. assumption.
Qed.

Theorem false_unproven : ~False.
Proof. unfold not. intros. inversion H.
Qed.

Theorem thm_true_imp_true : True -> True.
Proof.  reflexivity. Qed.

Theorem thm_false_imp_true : False->True.
Proof.
  intros proof_of_False. reflexivity.
Qed.

Theorem thm_true_imp_false : ~(True->False).
Proof.
  unfold not.
  intros  T_imp_F. destruct T_imp_F. reflexivity.
Qed.

Theorem absurd2 : (forall A C:Prop, A -> ~A->C).
Proof.
  unfold not. intros. destruct H0. assumption.
Qed.

Require Import Bool.

Theorem true_is_true : Is_true true.
Proof. reflexivity. Qed.

Theorem not_eqb_true_false : ~(Is_true (eqb true false)).
Proof.  simpl. apply false_unproven. Qed.

Theorem eqb_a_b : (forall a: bool, Is_true (eqb a a)).
Proof.
  intros. destruct a. reflexivity. reflexivity. Qed.

Theorem thm_eq_a_t : (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.  destruct a.
  reflexivity.
  simpl. intros. destruct H.
Qed.

Theorem left_or : (forall A B: Prop, A->A \/ B).
Proof.
  intros. left. assumption.
Qed.

Theorem right_o : (forall A B: Prop, B -> A \/ B).
Proof.
  intros. right. assumption.
Qed.

Theorem or_commutes : (forall A B:Prop, A\/B->B\/A).
Proof.
  intros A B A_or_B.
  destruct A_or_B as [proof_of_A|proof_of_B].
  right. assumption.
  left. assumption.
Qed.

Theorem both_and : (forall A B: Prop, A->B-> A/\B).
Proof.
  intros A B proof_of_A proof_of_B.
  split.
  assumption.
  assumption.
Qed.

Theorem and_commutes : (forall A B :Prop, A/\B -> B/\A).
Proof.
  intros A B H. destruct H as [Ha Hb].
  split. assumption. assumption.
Qed.

Theorem orb_is_or : (forall a b:bool, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b. destruct a,b.
  simpl. intuition.
  simpl. intuition.
  simpl. intuition.
  simpl. intuition.
Qed.

Theorem andb_is_and : (forall a b:bool, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros.
  destruct a,b.
  simpl. intuition.
  simpl. intuition.
  simpl. intuition.
  simpl. intuition.
Qed.

Theorem notb_is_not : (forall a:bool, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros. destruct a.
  simpl. intuition.
  simpl. intuition.
Qed.

Definition basic_predicate := (fun a => Is_true (andb a true)).

Theorem thm_exists_basics : ex basic_predicate.
Proof.
  unfold basic_predicate. exists true. reflexivity. Qed.

Theorem thm_forall_exists : (forall b:bool, (exists a:bool, Is_true(eqb a b))).
Proof.
  intros. exists b. destruct b. reflexivity. reflexivity. Qed.

Theorem eq_a_a : (forall a:bool, Is_true (eqb a a)).
Proof.  intros a. destruct a. reflexivity.  reflexivity. Qed.

Theorem forall_exists : (forall P: Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  unfold not. intros. destruct H0. apply (H x). assumption. Qed.

Theorem exists_forall : (forall P:Set->Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.  unfold not. intros. apply H. exists x. assumption. Qed.

Theorem exists_vs_forall : (forall P:Set->Prop, ~(exists x, P x) <-> (forall x, ~(P x))).
Proof.
  unfold not. split.
  intros. apply H. exists x. assumption.
  intros. destruct H0. apply (H x). assumption.
Qed.

Theorem thm_eq_sym : (forall x y: Set, x=y -> y=x).
Proof. intros. rewrite -> H. reflexivity. Qed.


Theorem thm_eq_tran : (forall x y z:Set, x=y->y=z->x=z).
Proof.  intros x y z x_y y_z. rewrite -> x_y. assumption. Qed.

Theorem andb_sym : (forall a b, a&&b = b&&a).
Proof. intuition. Qed.

Theorem neq_nega : (forall a, a <> (negb a)).
Proof. destruct a. intuition. intuition. Qed.

Theorem plus_2_3 : (S (S O)) + (S (S (S O))) = (S (S (S (S (S 0))))).
Proof.  reflexivity. Qed.

Theorem plus_O_n : (forall n, O + n = n).
Proof.   intros n.   reflexivity. Qed.

Theorem plus_n_O : (forall n, n + 0 = n).
Proof.
  induction n as [|n']. reflexivity. simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_sym : (forall n m, n+m=m+n).
Proof.
  intros n. induction n as [|n'].
  intros. simpl.  rewrite -> (plus_n_O m). reflexivity.
  intros. simpl. rewrite -> IHn'.
  induction m as [|m'].
  simpl. reflexivity.
  simpl. rewrite -> IHm'. reflexivity.
Qed.


Theorem minus_is_funny : (0-1)=(0-2).
Proof.  reflexivity. Qed.

Require Import List.

Theorem cons_add_one_to_length :
  (forall A:Type, (forall (x:A) (lst: list A), length (x::lst) = (S (length lst)))).
Proof.  intros A.  intros x lst.  reflexivity. Qed.

Definition hd(A:Type)(default:A)(l:list A) :=
  match l with
    | nil => default
    | x:: _ => x
  end.

Definition my_hd_for_nat_lists := hd nat 0.

Compute my_hd_for_nat_lists nil.
Compute my_hd_for_nat_lists (5::4::nil).

Theorem correctness_of_hd :
  (forall A:Type, (forall (default:A)(x:A)(lst:list A),
                ((hd A default nil) = default) /\ (hd A default (x::lst)) = x)).
Proof.
  intros A. intros. split. 
  reflexivity.
  reflexivity.
Qed.

Definition hd_error(A:Type)(l:list A):=
  match l with
    | nil => None
    | x::_ => Some x
  end.

Compute hd_error nat nil.
Compute hd_error nat (5::4::nil).

Theorem correctness_of_hd_error :
  (forall A:Type, (forall (x:A)(lst:list A),
                ((hd_error A nil) = None) /\ (hd_error A (x::lst))=Some x)).

Proof.
  intros A.  intros x lst. split.
  reflexivity.
  reflexivity.
Qed.

Definition hd_never_fail (A:Type)(lst:list A)(safety_proof:lst<>nil):A  :=
  (match lst as b return (lst = b->A) with
     | nil => (fun foo: lst = nil => match (safety_proof foo) return A with end)
     | x::_ => (fun foo: lst=x::_ => x)
   end) eq_refl.

Theorem correctness_of_hd_never_fail :
  (forall A:Type, (forall (x:A)(res:list A),
                (exists safety_proof: ((x::res)<>nil),
                   (hd_never_fail A (x::res) safety_proof)=x))).
Proof.
  intros A.  intros x res. 
  assert (witness : ((x::res)<>nil)).
  unfold not.  intros cons_eq_nil. inversion cons_eq_nil.
  exists witness. reflexivity.
Qed.

(* TODO review *)

  Definition tl (A:Type)(l:list A) :=
    match l with
      | nil => nil
      | a::m => m
    end.

  Theorem hd_tl :
    (forall A:Type,
       (forall (default:A)(x:A)(lst:list A),
          (hd A default (x::lst))::(tl A (x::lst))=(x::lst))).
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem app_nil_l : (forall A:Type, (forall l:list A, nil ++ l = l)).
  Proof.    intros.    reflexivity.  Qed.

  Theorem app_nil_r : (forall A:Type, (forall l:list A, l ++ nil = l)).
  Proof.
    intros. induction l as [|h l'].
    reflexivity.
    simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem app_comm_cons : forall A (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
  Proof.
    intros A x y. induction x as [|h x'].
    intros. simpl. reflexivity.
    intros. simpl. rewrite -> (IHx' h). reflexivity.
  Qed.

  Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
  Proof.
    intros A l m n.
    induction l as [|h l']. simpl. reflexivity.
    simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem app_cons_not_nil : forall A (x y:list A) (a:A), nil <> x ++ a :: y.
  Proof. intros. unfold not.
         induction x as [|h l'].
         intros. inversion H.
         simpl. intros. inversion H.
  Qed.
