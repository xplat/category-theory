Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".
Set Warnings "-unexpected-implicit-declaration".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Require Import Arith_base.
Require Vectors.Fin.

Module Shuffle.

Inductive t : nat -> nat -> Type :=
  | nil : t 0 0
  | skip : ∀ {p q : nat}, t p q -> t p (S q)
  | emit : ∀ {p q : nat}, t p (S q) -> t (S p) (S q).

(*
Definition cons {p q} (n : nat) : t p q -> t (S p) (n + q) :=
 fun v => let f := fix cons_fix nn vv {struct nn} :=
  match nn in nat return t p (nn + q) with
   | 0%nat => vv
   | S nnn => skip (cons_fix nnn vv)
  end
  in emit (f n v).
*)

Fixpoint get {p q} (it: t p q) (n : Fin.t p) : Fin.t q :=
  (fun f => f n) match it in t p q return Fin.t p -> Fin.t q with
    | nil => fun devil => devil
    | @skip p q rest => fun n => Fin.FS (get rest n)
    | @emit p0 q rest => fun n1 => (fun f => f rest) match n1 in Fin.t (S p0) return t p0 (S q) -> Fin.t (S q) with
        | Fin.F1 => fun _ => Fin.F1
        | Fin.FS n2 => fun rest => Fin.FS (@get p (S q) rest n2)
      end
  end.

(******************************************
  BIG ERROR BIG ERROR BIG ERROR BIG ERROR
 ******************************************
In environment
get : ∀ p q : nat, t p q → Fin.t p → Fin.t q
p : nat
q : nat
it : t p q
n : Fin.t p
p0 : nat
q0 : nat
rest : t p0 (S q0)
n1 : Fin.t (S p0)
n0 : nat
n2 : Fin.t n0
rest0 : t n0 (S q0)
The term "rest0" has type "t n0 (S q0)" while it is expected to have type "t p (S q0)".
Not in proof mode.
*)





Section SCHEMES.

(*
Definition rectS (P:∀ {p q}, t (S p) q -> Type)
 (bas: ∀ (q : nat) (tl : t 0 q), P (emit tl))
 (rect: ∀ a {p q} (v: t (S p) q), P v -> P (cons a v)) :=
 fix rectS_fix {n p q} (v: t (S p) q) : P v :=
 match v with
 |@emit 0 a v => bas (emit v)
 |@emit (S nn') a v => rect a v (rectS_fix v)
 |@
 |_ => fun devil => False_ind (@IDProp) devil
 end.

A vector of length 0 is nil
Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v :=
match v with
  |[] => H
  |_ => fun devil => False_ind (@IDProp) devil
end.

A vector of length S _ is cons
Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil
end.

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

An induction scheme for 2 vectors of same length
Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) :=
  fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
  match v1 with
  | [] => fun v2 => case0 _ bas v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
  end.
*)

End SCHEMES.

Program Instance Δ : Category := {|
  obj := nat;
  hom := Shuffle.t;
  homset x y := {| equiv := _; |};
  id x := _;
|}.
Next Obligation. (* id x *)
induction x.
- exact nil.
- apply skip.  now apply emit.
