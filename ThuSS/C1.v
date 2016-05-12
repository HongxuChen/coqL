Fixpoint fact (n:nat) :=
  match n with
    | 0 => 1
    | S p => n * fact(p)
  end.

Compute fact(6).

Require Import ZArith.

Check (3, Z0, xH, xI, xO, Zpos, (xO  xH)).

(* Eval compute in *)
(*     iter 6 (nat*nat) (fun p => let (x, r) :=  p in (x+1, (x+1)*r) (0,1)). *)

(* notations *)
Locate "_ * _".

(* Theorems *)
SearchAbout "_ * _".

Require Import List.

Compute (1::2::nil) ++ (3::nil).

Compute fold_right (fun x y => x*y) 5 (1::2::3::nil).
