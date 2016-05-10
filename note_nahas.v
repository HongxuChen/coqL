(* a note from https://coq.inria.fr/tutorial-nahas;
original coq file: https://github.com/coq/www/blob/master/files/nahas_tutorial.v *)

Theorem hw_proof : (forall A B: Prop, A->(A->B)->B).
Proof.
  intros A B A_implies_B.
  intros proof_of_A.
  pose (proof_of_B := proof_of_A A_implies_B).
  exact proof_of_B.
Qed.

Theorem hw_proof_bwd : (forall A B: Prop, A->(A->B)->B).
Proof.
  intros A B proof_of_A A_implies_B.
  refine (A_implies_B _).
  exact proof_of_A.
Qed.

Theorem hw_proof_more_bwd : (forall A B C: Prop, A->(A->B)->(B->C)->C).
Proof.
  intros A B C proof_of_A A_implies_B B_implies_C.
  refine (B_implies_C _).
    refine (A_implies_B _).
      exact proof_of_A.
Qed.

Theorem bwd_huge : (forall A B C: Prop, A->(A->B)->(A->B->C)->C).
Proof.
  intros A B C proof_of_A A_implies_B A_imp_B_imp_C.
  refine (A_imp_B_imp_C _ _).
  (* 1st subgoal: A *)
  exact proof_of_A.
  (* 2nd subgoal: B *)
  refine (A_implies_B _).
  exact proof_of_A.
Show Proof.
Qed.  

Theorem fwd_huge : (forall A B C: Prop, A->(A->B)->(A->B->C)->C).
Proof.
  intros A B C proof_of_A A_imp_B A_imp_B_imp_C.
  pose (proof_of_B := A_imp_B proof_of_A).
  pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
  exact proof_of_C.
Show Proof.
Qed.  

Theorem self_proof : (forall A: Prop, A->A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

Theorem true_proven : True.
exact I.
Qed.

Theorem false_unproven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem false_unproven_again : ~False.
Proof.
  intros proof_of_False.
  case proof_of_False.
Qed.

Theorem thm_true_imp_true : True -> True.
Proof.
  intros proof_of_True.
  exact I.
Qed.

Theorem thm_false_imp_true : False->True.
Proof.
  intros proof_of_False.
  exact I.
Qed.

Theorem thm_true_imp_false : ~(True->False).
Proof.
  unfold not.
  intros  T_imp_F.
  refine (T_imp_F _).
  exact I.
Qed.

Theorem absurd2 : (forall A C:Prop, A -> ~A->C).
Proof.
  intros A C.
  intros proof_of_A proof_that_A_unproven.
  unfold not in proof_that_A_unproven.
  pose (proof_of_False := proof_that_A_unproven proof_of_A).
  case proof_of_False.
Qed.

Require Import Bool.

Theorem true_is_true : Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false : ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact false_unproven.
Qed.

Theorem eqb_a_b : (forall a: bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
  (* suppose a is true *)
  simpl.
  exact I.
  (* suppose a is false *)
  simpl.
  exact I.
Qed.

Theorem thm_eq_a_t : (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  (* suppose a is true *)
  case a.
  simpl.
  intros proof_of_True.
  exact  I.

  simpl.
  intros proof_of_False.
  case proof_of_False.
Qed.  

Theorem left_or : (forall A B: Prop, A->A \/ B).
Proof.
  intros A B proof_of_A.
  pose (proof_of_A_or_B := or_introl proof_of_A: A \/ B).
  simpl.
  exact proof_of_A_or_B.
Qed.

Theorem right_o : (forall A B: Prop, B -> A \/ B).
Proof.
  intros A B proof_of_B.
  refine (or_intror _).
  exact proof_of_B.
Qed.

Theorem or_commutes : (forall A B:Prop, A\/B->B\/A).
Proof.
  intros A B A_or_B.
  case A_or_B.
  (* suppose A_or_B is (or_introl proof_of_A)*)
  intros proof_of_A.
  refine (or_intror _).
  exact proof_of_A.
  (* suppose A_or_B is (or_intror proof_of_B) *)
  intros proof_of_B.
  refine (or_introl _).
  exact proof_of_B.
Qed.

Theorem both_and : (forall A B: Prop, A->B-> A/\B).
Proof.
  intros A B proof_of_A proof_of_B.
  refine (conj _ _).
  exact proof_of_A.
  exact proof_of_B.
Qed.

Theorem and_commutes : (forall A B :Prop, A/\B -> B/\A).
Proof.
  intros A B A_and_B.
  case A_and_B.
  intros proof_of_A proof_of_B.
  refine (conj _ _).
  exact proof_of_B.
  exact proof_of_A.
Qed.

Theorem and_commutes_again : (forall A B:Prop, A/\B -> B/\A).
Proof.
  intros A B A_and_B.
  destruct A_and_B as [proof_of_A proof_of_B] (* conj *).
  refine (conj _ _).
  exact proof_of_B.
  exact proof_of_A.
Qed.

Theorem orb_is_or : (forall a b:bool, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold  iff.
  (* orb -> \/ *)
  refine (conj _ _).
  case a,b.
  (* a,b is true, true *)
  simpl.
  intros proof_of_true.
  refine (or_introl _).
  exact I.
  simpl.
  (* a,b is true, false *)
  simpl.
  intros proof_of_true.
  refine (or_introl _).
  exact I.
  (* a,b is false, true *)
  simpl.
  intros proof_of_true.
  refine (or_intror _).
  exact  I.
  (* a,b is false, false *)
  simpl.
  intros proof_of_false.
  case proof_of_false.

  (* \/ -> orb *)
  intros H.
  case a,b.
  simpl.
  exact I.
  simpl.
  exact I.
  simpl.
  exact I.
  simpl.
  case H.
  simpl.
  intros proof_of_false.
  case proof_of_false.
  simpl.
  intros proof_of_false.
  case proof_of_false.
  Qed.

Theorem andb_is_and : (forall a b:bool, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  unfold iff.
  intros a b.
  refine (conj _ _).
  (* andb -> a/\b *)
  simpl.
  case a, b.
  
  intros H.
  refine (conj _ _).
  simpl.
  exact I.
  simpl.
  exact I.
  
  intros H.
  simpl in H.
  case H.

  intros H.
  simpl in H.
  case H.
  
  intros H.
  simpl in H.
  case H.

  (* a/\b -> andb *)
  intros H.
  case a, b.
  simpl.
  exact I.

  simpl.
  simpl in H.
  case H.
  intros proof_of_true proof_of_false.
  case proof_of_false.

  simpl.
  simpl in H.
  case H.
  intros proof_of_false.
  case proof_of_false.

  simpl.
  simpl in H.
  case H.
  intros proof_of_false_1.
  case proof_of_false_1.
  
Qed.

Theorem notb_is_not : (forall a:bool, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros a.
  case a.

  (* suppose a is true *)
  unfold iff.
  refine (conj _ _).
  simpl.
  unfold not.
  intros proof_of_false.
  case proof_of_false.

  simpl.
  unfold not.
  intros H.
  destruct H.
  exact I.

  (* suppose a is false *)
  simpl.
  refine (conj _ _).
  unfold not.
  intros proof_of_true proof_of_false.
  case proof_of_false.

  unfold not.
  intros H.
  exact I.
Qed.
  
Definition basic_predicate := (fun a => Is_true (andb a true)).

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
  simpl.
  exact I.
Qed.

Theorem thm_exists_basics_again : (exists a:bool, Is_true (andb a true)).
Proof.
  pose (witness := true).
  refine (ex_intro _ witness _).
  simpl.
  exact I.
Qed.

Theorem thm_forall_exists : (forall b:bool, (exists a:bool, Is_true(eqb a b))).
Proof.
  intros b.
  case b.
  
  pose (witness := true).
  refine (ex_intro _ witness _).
  simpl.
  exact I.

  pose (witness := false).
  refine (ex_intro _ witness _).
  simpl.
  exact I.
Qed.


Theorem eq_a_a : (forall a:bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
  simpl.
  exact I.
  simpl.
  exact I.
Qed.  

Theorem thm_forall_exists_again : (forall b:bool, (exists a:bool, Is_true(eqb a b))).
Proof.
  intros b.
  refine (ex_intro _ b _).
  exact (eq_a_a b).
Qed.


Theorem forall_exists : (forall P: Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P.
  unfold not.
  intros forall_x_not_Px exists_x_Px.
  destruct exists_x_Px as [witness proof_of_Pwitness]. (* ex_intro P *)
  pose (not_Pwitness := forall_x_not_Px witness).
  pose (proof_of_false := not_Pwitness proof_of_Pwitness).
  case proof_of_false.
Qed.

Theorem exists_forall : (forall P:Set->Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
  intros P.
  unfold not.
  intros not_exists_x_Px x Px.
  refine (not_exists_x_Px _).
  exact (ex_intro P x Px).
Qed.

Theorem exists_vs_forall : (forall P:Set->Prop, ~(exists x, P x) <-> (forall x, ~(P x))).
Proof.
  intros P.
  unfold iff.
  unfold not.
  refine (conj _ _).
  
  intros not_exists_x_Px x P_x.
  refine (not_exists_x_Px _).
  exact (ex_intro P x P_x).

  intros forall_x_not_Px exists_x_Px.
  destruct exists_x_Px as [witness P_witness].
  pose (not_P_witness := forall_x_not_Px witness).
  pose (proof_of_false := not_P_witness P_witness).
  case proof_of_false.

Qed.

Theorem thm_eq_sym : (forall x y: Set, x=y -> y=x).
Proof.
  intros x y x_y.
  destruct x_y as [].
  exact (eq_refl x).
Qed.


Theorem thm_eq_tran : (forall x y z:Set, x=y->y=z->x=z).
Proof.
  intros x y z x_y y_z.
  destruct x_y as [].
  destruct y_z as [].
  exact (eq_refl x).
Qed.

Theorem thm_eq_tran_again : (forall x y z:Set, x=y->y=z->x=z).
Proof.
  intros x y z.
  intros x_y y_z.
  rewrite x_y.
  rewrite <- y_z.
  exact (eq_refl y).
Qed.

Theorem andb_sym : (forall a b, a&&b = b&&a).
Proof.
  intros a b.
  case a, b.
  simpl.
  exact (eq_refl true).
  simpl.
  exact (eq_refl false).
  simpl.
  exact (eq_refl false).
  simpl.
  exact (eq_refl false).
  Qed.

Theorem neq_nega : (forall a, a <> (negb a)).
Proof.
  intros a.
  unfold not.
  case a.
  intros a_eq_neg_a.
  simpl in a_eq_neg_a.
  discriminate a_eq_neg_a.
  intros a_eq_neg_a.
  simpl in a_eq_neg_a.
  discriminate a_eq_neg_a.
Qed.

Theorem plus_2_3 : (S (S O)) + (S (S (S O))) = (S (S (S (S (S 0))))).
Proof.
  simpl.
  exact (eq_refl 5).
Qed.

Theorem plus_O_n : (forall n, O + n = n).
Proof.
  intros n.
  simpl.
  exact (eq_refl n).
Qed.

Check nat_ind.

Theorem plus_n_O : (forall n, n + 0 = n).
Proof.
  intros n.
  elim n.

  (* base case *)
  simpl.
  exact (eq_refl O).

  (* inductive cases *)
  intros n0 inductive_H.
  simpl.
  rewrite inductive_H.
  exact (eq_refl (S n0)).
Qed.


Theorem plus_sym : (forall n m, n+m=m+n).
Proof.
  intros n m.
  elim n.
  (* base for n *)
  simpl.
  elim m.
  (* base for m *)
  simpl.
  exact (eq_refl O).
  (* inductive for m *)
  intros m'.
  simpl.
  intros inductive_hyp_m.
  rewrite <- inductive_hyp_m.
  exact (eq_refl (S m')).

  (* inductive for n *)
  intros n' inductive_hyp_n.
  simpl.
  rewrite inductive_hyp_n.
  elim m.
  (* base for m *)
  simpl.
  exact (eq_refl (S n')).
  (* inductive for m *)
  intros m'.
  simpl.
  intros inductive_hyp_m.
  rewrite inductive_hyp_m.
  exact (eq_refl (S (m'+S n'))).
Qed.


Theorem minus_is_funny : (0-1)=(0-2).
Proof.
  simpl.
  exact (eq_refl 0).
Qed.

Require Import List.

Theorem cons_add_one_to_length :
  (forall A:Type, (forall (x:A) (lst: list A), length (x::lst) = (S (length lst)))).
Proof.
  intros A.
  intros x lst.
  simpl.
  exact (eq_refl (S (length lst))).
Qed.

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
  intros A.
  intros default x lst.
  refine (conj _ _).
  simpl.
  exact (eq_refl default).
  simpl.
  exact (eq_refl x).
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
  intros A.
  intros x lst.
  refine (conj _ _).
  simpl.
  exact (eq_refl None).
  simpl.
  exact (eq_refl (Some x)).
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
  intros A.
  intros x res.
  assert (witness : ((x::res)<>nil)).
  unfold not.
  intros cons_eq_nil.
  discriminate cons_eq_nil.
  refine (ex_intro _ witness _).
  simpl.
  exact (eq_refl x).
  
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
  intros A.
  intros default x lst.
  simpl.
  exact (eq_refl (x::lst)).
Qed.

Theorem app_nil_l : (forall A:Type, (forall l:list A, nil ++ l = l)).
Proof.
  intros A.
  intros l.
  simpl.
  exact (eq_refl l).
Qed.

Theorem app_nil_r : (forall A:Type, (forall l:list A, l ++ nil = l)).
Proof.
  intros A.
  intros l.
  elim l.
  (* base case for l *)
  simpl.
  exact (eq_refl nil).
  (* inductive for l *)
  intros a l' inductive_hyp.
  simpl.
  rewrite inductive_hyp.
  exact (eq_refl (a::l')).
Qed.

Theorem app_comm_cons : forall A (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros A.
  intros x y a.
  elim x.
  (* base for x *)
  simpl.
  exact (eq_refl (a::y)).
  (* inductive for x *)
  intros a' x' inductive_hyp_x.
  simpl.
  exact (eq_refl (a::a'::x'++y)).
  Qed.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  elim l.
  simpl.
  exact (eq_refl (m++n)).
  intros a l' inductive_hyp_l.
  simpl.
  rewrite <- inductive_hyp_l.
  exact (eq_refl (a::l'++m++n)).
  Qed.

Theorem app_cons_not_nil : forall A (x y:list A) (a:A), nil <> x ++ a :: y.
Proof.
  unfold not.
  destruct x as [| head tail];simpl;intros.
  discriminate H.
  discriminate H.
Qed.
