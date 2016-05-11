(*
C-c C-c         proof-interrupt-process
C-c C-f         proof-find-theorems
C-c C-l         proof-layout-windows
C-c C-n         proof-assert-next-command-interactive
C-c C-o         proof-display-some-buffers
C-c C-p         proof-prf
C-c C-u         proof-undo-last-successful-command
C-c C-v         proof-minibuffer-cmd
C-c C-w         pg-response-clear-displays
C-c C-x         proof-shell-exit
C-c `           proof-next-error
C-c C-.         proof-goto-end-of-locked

C-c C-a C-a     coq-SearchAbout
C-c C-a C-b     coq-About
C-c C-a C-c     coq-Check
C-c C-a C-o     coq-SearchIsos
C-c C-a C-p     coq-Print
C-c C-a C-s     coq-Show
C-c C-a g       proof-store-goals-win
C-c C-a h       coq-PrintHint
C-c C-a r       proof-store-response-win
 *)

(* chapter 1 *)
Check (fun x:nat => x=3).
Check (forall x:nat, x<=3 \/ (exists y:nat, x = y + 3)).

Check let f := fun x:nat => (x*3, x) in f 3.

Locate "_ <= _".

Check and.

Check (and True False).

Check (and True).

Eval compute in let f := fun x => (x*3, x) in f 3.

(* exercise *)
Definition fun1 := fun a b c d e => a+b+c+d+e.
Print fun1.
Eval compute in fun1 1 2 3 4 5.
Reset fun1.
Definition fun1 a b c d e := a+b+c+d+e.
Print fun1.
Check fun1.
Compute fun1 1 2 3 4 5.

(* chapter 2 *)
Require Import Bool.

Eval compute in if true then 3 else 5.
Search bool.
(* SearchHead bool. *)

Require Import Arith.

Definition is_zero (n:nat):=
  match n with
    | 0 => true
    | S p => false
  end.

Fixpoint sum_n n :=
  match n with
    | 0 => 0
    | S p => p + sum_n p
  end.
Compute (sum_n 10).

Fixpoint sum_n_s n s :=
  match n with
    | 0 => s
    | S p => (sum_n_s p (p+s))
  end.
Compute (sum_n_s 10 0).

Fixpoint evenb n :=
  match n with
    | 0 => true
    | 1 => false
    | S (S p) => evenb p
  end.
Compute (evenb 3).
Compute (evenb 10).

Require Import List.

Check 1::2::3::nil.
(* different from  what totorial said *)
Check nil.
Check (nil: list nat).

Compute map (fun x => x+3) (1::2::3::nil).
Compute map S (1::2::nil).
Compute let l :=  (1::2::3::nil) in l ++ map (fun x=>x+100) l.

(* exercise *)

Fixpoint range_inner (n:nat) (m:nat) : (list nat) :=
  match n with
    | 0 => nil
    | S p => m::(range_inner p (m+1))
  end.
Definition range (n:nat) := range_inner n 0.
Compute (range 10).

Definition head_evb l :=
  match l with
    | nil => false
    | h::_ => evenb h
  end.
Compute head_evb (1::2::3::nil).
Compute head_evb (2::3::nil).

Fixpoint sum_list (l:(list nat)) :=
  match l with
    | nil => 0
    | h::t => h + (sum_list t)
  end.
Compute (sum_list (1::2::3::nil)).

Fixpoint insert n l :=
  match l with
    | nil => n::nil
    | h::t => if (leb n h) then n::l else h::(insert n t)
  end.
Fixpoint sort l :=
  match l with
    | nil => nil
    | h::t => insert h (sort t)
  end.
Compute (sort (3::4::2::nil)).


Check le_n.
Check le_S.

Theorem three_le_five : 3<=5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Require Import Arith.

Check le_trans.

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
  intros.
  apply le_trans with (m := 10).
  assumption.
  assumption.
Qed.

SearchRewrite (_ + (_ + _)).

Lemma example6 : forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.
Proof.
  intros.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_r.
  rewrite plus_assoc.
  rewrite <- plus_assoc with (n := x*x).
  rewrite mult_comm with (n:=y) (m:=x).
  pattern (x*y) at 1; rewrite <- mult_1_l.
  rewrite <- mult_succ_l.
  rewrite mult_assoc.
  reflexivity.
Qed.

Require Import Omega.

Lemma omega_example :
  forall f x y, 0 < x -> 0 < f x -> 3 * f x <= 2 * y -> f x <= y.
Proof.
  intros. omega.
Qed.

Fixpoint sum_n n :=
  match n with
      0 => 0
    | S p => p + sum_n p
  end.

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
Proof.
  induction n.
  simpl.
  reflexivity.
  assert (SnSn : S n * S n = n * n + 2 * n + 1).
  ring.
  rewrite SnSn.
  rewrite <- IHn.
  simpl.
  ring.
Qed.