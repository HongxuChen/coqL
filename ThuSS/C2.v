Inductive month :=
| Jan | Feb | Mar | Apr | May | Jun
| Jul | Aug | Sep | Oct | Nov | Dec.

Definition nbdays m :=
  match m with
    | Apr => 30 | Jun => 30 | Sep => 30 | Nov => 30 | Feb => 28 | _ => 31
    end.

Compute nbdays(Jul).

Inductive i_plane : Type := point (x y :nat).
Check i_plane.
Definition point_x p := match p with point x _ => x end.
Definition point_y p := match p with point _ y => y end.
Compute point_x (point 2 3).
Compute point_y (point 2 3).

Require Import String.

Inductive t1 : Type :=
| c1t1 (n:nat)(s:string)
| c2t1 (n:nat).

Definition ft1 (v:t1) :=
  match v with
    | c1t1 a s => a
    | c2t1 n => n
  end.

Compute (ft1 (c1t1 3 "good")).
Compute (ft1 (c2t1 4)).

Fixpoint plus (n m:nat) :=
  match n with
    | O => m
    | S p => S (plus p m)
  end.

Compute plus 30 40.

Fixpoint minus (n m : nat) :=
  match n, m with
    | _ , 0 => n
    | 0 , _ => 0
    | S p , S q => minus p q
  end.

Notation "x - y" := (minus x y).
Compute 4-5.
Compute 5-4.
