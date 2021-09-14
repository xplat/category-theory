Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".
Set Warnings "-unexpected-implicit-declaration".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Require Import Arith.
Require Import Lia.
Local Open Scope nat_scope.

Definition Fin (n : nat) := {k: nat | k < n}.
Definition Vec t n := {ts: list t | length ts = n}.

Module Monotonic.
Record t (p q : nat) : Type := {
    carrier :> Fin p -> Fin q;
    is_monotonic : ∀ (n1 n2 : Fin p), ` n1 <= ` n2 -> ` (carrier n1) <= ` (carrier n2);
}.

Program Definition id p : t p p := {|
    carrier := fun n => n;
|}.

Program Definition compose p q r : t q r -> t p q -> t p r := fun g f => {|
    carrier := g \o f;
|}.
Next Obligation.
now repeat apply is_monotonic.
Qed.

Program Definition vertex n (k : Fin (S n)) : t 1 (S n) := {|
  carrier i := i + k;
|}.
Next Obligation.
destruct i as [i i_ok].  destruct k as [k k_ok].  simpl.  lia.
Defined.
Next Obligation.
destruct k, n1, n2.  simpl in * |- *.  lia.
Qed.

Program Definition edge n (k : Fin n) : t 2 (S n) := {|
  carrier i := i + k;
|}.
Next Obligation.
destruct i as [i i_ok].  destruct k as [k k_ok].  simpl.  lia.
Defined.
Next Obligation.
destruct k, n1, n2.  simpl in * |- *.  lia.
Qed.

Program Definition setoid p q : Setoid (t p q) := {|
    equiv (f g : t p q) := ∀ n, f n = g n;
|}.
Next Obligation.
equivalence.  now transitivity (y n).
Qed.

End Monotonic.

Coercion Monotonic.carrier: Monotonic.t >-> Funclass.

(* succ everything so we don't get the augmented simplex category and to match convention *)
Program Instance Δ : Category := {|
  obj := nat;
  hom x y := Monotonic.t (S x) (S y);
  homset x y := Monotonic.setoid (S x) (S y);
  id x := Monotonic.id (S x);
  compose x y z := Monotonic.compose (S x) (S y) (S z);
|}.
Next Obligation.
intros f0 f1 f0_eq_f1 g0 g1 g0_eq_g1 n.  simpl.  rewrite g0_eq_g1.  apply f0_eq_f1.
Qed.

Require Import Category.Instance.Sets.
Require Import Category.Theory.Sheaf.
Require Import Category.Functor.Hom.

Definition SSets : Category := @Presheaves Δ Sets.

Definition SimplicialSimplex n : Presheaf Δ Sets := [Hom n,─].

Eval hnf in 3 ~{ Δ^op }~> 6.

Program Definition Horn n (k : Fin (S n)) : Presheaf Δ Sets := {|
  fobj x := {|
    carrier := { f: n ~{ Δ^op }~> x | ¬ ∀ (j : Fin (S n)), (`j) ≠ (`k) -> ¬ ∀ (i : Fin (S x)), ¬ (@eq nat (f i) j) };
    is_setoid := {|
      equiv := @equiv _ (Monotonic.setoid (S x) (S n));
    |};
  |};
  fmap x y f := {| morphism g := Monotonic.compose (S y) (S x) (S n) g f; |};
|}.

Print "=".
Next Obligation.
equivalence.
now transitivity (`y n0).
Qed.
Next Obligation.
intros untrue.  apply H.
intros j j_ne_k untrue_too.  apply (untrue j).
- easy.
- intros i.  apply (untrue_too (f i)).
Qed.
Next Obligation.
intros f0 f1 f0_eq_f1 g i.  simpl.  now rewrite f0_eq_f1.
Qed.

Program Definition HornIncl n k : Horn n k ~{ SSets }~> SimplicialSimplex n := {|
  transform x := {| morphism f := f; |};
  naturality := _;
|}.

Section Example_1_1_1_1.

End Example_1_1_1_1.

Section Example_1_1_1_2.

End Example_1_1_1_2.

Section Example_1_1_1_3.

End Example_1_1_1_3.

Section Example_1_1_1_4.

End Example_1_1_1_4.

Section Convention_1_1_1_5.

End Convention_1_1_1_5.

Section Definition_1_1_1_6.

End Definition_1_1_1_6.

Section Remark_1_1_1_7.

End Remark_1_1_1_7.

Section Definition_1_1_2_1.

Class KanComplex (cplx: obj[ SSets ]) : Type := {
  lift_horn: ∀ {n k}, (Horn n k ~{ SSets }~> cplx) -> SimplicialSimplex n ~{ SSets }~> cplx;
  lift_horn_commutes: ∀ n k (f : Horn n k ⟹ cplx), lift_horn f ∘ HornIncl n k ≈ f;
}.

End Definition_1_1_2_1.

Section Proposition_1_1_2_2.

Program Definition CategorialSimplex n : Category := {|
  obj := Fin (S n);
  hom x y := x <= y;
  homset x y := {| equiv x y := True; |};
|}.
Next Obligation.
destruct x, y, z in * |- *. simpl in * |- *. lia.
Qed.

Require Import Category.Instance.Cat.

Program Definition CategorialSimplices : Δ ⟶ Cat := {|
  fobj := CategorialSimplex;
  fmap x y f := {|
    fobj k := f k;
    fmap a b g := _;
  |};
|}.
Next Obligation.
now apply Monotonic.is_monotonic.
Defined.
Next Obligation.
intros f0 f1 f0_eq_f1.  simpl.  constructor.
- intros.  rewrite f0_eq_f1.  apply iso_id.
- easy.
Qed.

Require Import Category.Instance.Fun.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import PeanoNat.

Program Definition RestrictBy {C D E : Category} (F : C ⟶ D) : [ D , E ] ⟶ [ C , E ] := {|
  fobj X := Compose X F;
  fmap X Y η := whisker_right η F;
|}.

Program Definition Nerve : Cat ⟶ SSets := Compose (RestrictBy (CategorialSimplices^op)) (Curried_CoHom Cat).

Program Definition InnerHorn (n k : nat) {k_ok : 0 < k < n} : obj[ SSets ] := Horn n k.

Program Definition InnerHornIncl (n k : nat) {k_ok : 0 < k < n} : @InnerHorn n k k_ok ~{ SSets }~> SimplicialSimplex n := HornIncl n k.

Inductive path1p (C : Category) (x: C) : C -> Type :=
  | path1p_nil : path1p C x x
  | path1p_trans {y z} : C y z -> path1p C x y -> path1p C x z.

Program Definition vertex_from_horn C n k k_ok : @InnerHorn n k k_ok ~{ SSets }~> Nerve C -> ∀ (i : Fin (S n)), obj[C] :=
  fun horn_incl i => @fobj (CategorialSimplex 0) C (transform horn_incl 0 (Monotonic.vertex n i)) 0.
Next Obligation.
intros untrue.
destruct i as [i i_ok].  destruct i.
- apply (untrue (@exist _ _ n (le_n (S n)))).
  + simpl.  intros untrue_too.  clear horn_incl.  rewrite <- untrue_too in *.  lia.
  + intros [m m_ok].  simpl.  lia.
- apply (untrue (@exist _ _ 0 (Nat.lt_0_succ n))).
  + intros untrue_too.  simpl in untrue_too.  clear horn_incl.  clear untrue.  now rewrite <- untrue_too in *.
  + intros m.  simpl.  lia.
Qed.

(*************************************** WORKS UNTIL HERE *****************************************************)

Definition partial_spine_from_horn C n k k_ok (horn_incl: @InnerHorn n k k_ok ~{ SSets }~> Nerve C) (i: nat) i_ok
    : path1p C (vertex_from_horn C n k k_ok horn_incl (exist _ 0 (Nat.lt_0_succ n))) (vertex_from_horn C n k k_ok horn_incl (exist _ i i_ok)).
induction i.
- simpl.  eapply path1p_nil.

Definition spine_from_horn C n k k_ok : @InnerHorn n k k_ok ~{ SSets }~> Nerve C -> { x & {y & path1p C x y }}.
intros horn_incl.  unshelve (esplit; esplit).

Program Definition ExtendInnerVee C : @InnerHorn 2 1 _ ~{ SSets }~> Nerve C -> SimplicialSimplex 2 ~{ SSets }~> Nerve C := fun vee => {|
  transform := let y := @morphism _ _ _ _ (transform vee 0) in ltac:(simpl in y; idtac);
|}.
Next Obligation.
destruct vee.  revert x.  simpl in * |- *.  edestruct transform.  simpl in morphism.

Class Nervy (nrv: obj[ SSets ]) : Type := {
  perp_inner_horn: ∀ {n k} {k_ok: 0 < k < n} (f : @InnerHorn n k k_ok ~{ SSets }~> nrv),
    exists! (r: SimplicialSimplex n ~{ SSets }~> nrv), inhabited (r ∘ @InnerHornIncl n k k_ok ≈ f);
  (* XXX may need another member to recover the proof of equality relevantly *)
}.

Definition Nervy_if_nerve (K: obj[ SSets ]): {C & Isomorphism K (Nerve C)} -> Nervy K.
intros [C iso].  constructor.  intros *.  destruct n; try lia.  destruct n; try lia.  induction n.
- destruct k_ok as [bigger smaller].  destruct k in * |- *; dependent destruction bigger; try lia.
  (* this is the meaty case; the inner horn of the triangle *)
  unshelve (eapply ex_intro; split).
  + unshelve (eapply Build_Transform).
unshelve (eapply ex_intro; split).
-

Definition Nerve_if_nervy (K: obj[ SSets ]): Nervy K -> {C & Isomorphism K (Nerve C)}.
Admitted.

(*
Module Shuffle.

Inductive pre_t : Type :=
  | nil : pre_t
  | emit : pre_t -> pre_t
  | skip : pre_t -> pre_t.

Definition empty (it : pre_t) : Prop :=
  match it with
    | nil => True
    | _ => False
  end.

Fixpoint wf (it: pre_t) : Prop :=
  match it with
    | nil => True
    | emit rest => ¬ empty rest /\ wf rest
    | skip rest => wf rest
  end.

Fixpoint length (it : pre_t) : nat :=
  match it with
    | nil => 0
    | emit rest => S (length rest)
    | skip rest => length rest
  end.

Fixpoint colength (it : pre_t) : nat :=
  match it with
    | nil => 0
    | emit rest => colength rest
    | skip rest => S (colength rest)
  end.

Lemma nonempty_is_colong (it : pre_t) : (¬ empty it /\ wf it) -> colength it > 0.
Proof.
    induction it.
    - tauto.
    - simpl.  tauto.
    - simpl.  lia.
Qed.

Definition t (len colen : nat) : Type := { pre : pre_t | wf pre /\ length pre = len /\ colength pre = colen }.

Program Fixpoint get_internal (p q : nat) (it: pre_t) (is_wf: wf it) (len : length it = p) (colen : colength it = q) (n : Fin p) {struct it}: Fin q :=
  match it with
    | nil => False_rect (Fin q) _
    | skip rest => S (` @get_internal p (q - 1) rest _ _ _ n)
    | emit rest => match n with
        | 0 => 0
        | S nnext => @get_internal (p - 1) q rest _ _ _ nnext
      end
  end.
Next Obligation.
destruct n. lia.
Qed.
Next Obligation.
lia.
Qed.
Next Obligation.
lia.
Defined.
Next Obligation.
now apply nonempty_is_colong.
Qed.
Next Obligation.
lia.
Qed.
Next Obligation.
simpl.
destruct rest.
- tauto.
- destruct n as [nval nlim].  simpl in *.  lia.
- destruct n as [nval nlim].  simpl in *.  lia.
Qed.

Definition get {p q} (it: t p q) (n: Fin p): Fin q :=
  ltac:(destruct it as [X [Y [Z W]]]; exact (get_internal p q X Y Z W n)).

Program Fixpoint compose_internal {p q r}
    (this: pre_t) (this_wf: wf this) (this_len: length this = q) (this_colen: colength this = r)
    (that: pre_t) (that_wf: wf that) (that_len: length that = p) (that_colen: colength that = q) {struct that}: t p r :=
  match that with
    | nil => this
    | emit rest => emit (compose_internal this this_wf this_len this_colen rest _ _ _)
    | skip rest => compose_skip this this_wf this_len this_colen rest _ _ _
  end
with compose_skip {p q r}
    (this: pre_t) (this_wf: wf this) (this_len: length this = q) (this_colen: colength this = r)
    (that: pre_t) (that_wf: wf that) (that_len: length that = p) (that_colen: colength that = q) {struct this}: t p r :=
  match this with
    | nil => nil
    | emit rest => compose_internal rest _ _ _ that that_wf that_len that_colen
    | skip rest => skip (compose_skip rest _ _ _ that that_wf that_len that_colen)
  end.
  (*
Inductive t : nat -> nat -> Type :=
  | nil : t 0 0
  | skip : ∀ {p q : nat}, t p q -> t p (S q)
  | emit : ∀ {p q : nat}, t p (S q) -> t (S p) (S q).

(*
Program Definition cons {p q} (n : nat) : t p q -> t (S p) (n + q) :=
 fun v => let f := fix cons_fix nn vv {struct nn} :=
  match nn in nat return t p (nn + q) with
   | 0%nat => vv
   | S nnn => skip (cons_fix nnn vv)
  end
  in @emit _ q (f n v).

Next Obligation.
induction n.
*)

Program Fixpoint get {p q} (it: t p q) (n : Fin p) : Fin q :=
  (fun f => f n) match it in t p q return Fin p -> Fin q with
    | nil => fun devil => devil
    | @skip p1 q1 rest => fun n1 => S (get rest n1)
    | @emit p1 q1 rest => fun n1 => match n1 with
        | 0 => 0
        | S n2 => get rest n2
      end
  end.

Next Obligation.
lia.
Defined.
Next Obligation.
lia.
Defined.
Next Obligation.
destruct n1 in * |- *.
simpl in * |- *.
lia.
Defined.

Lemma get_is_monotone : ∀ p q (it: t p q) (n1 n2: Fin p), proj1_sig n1 <= proj1_sig n2 -> proj1_sig (get it n1) <= proj1_sig (get it n2).
Proof.
  intros * n1_le_n2.
  induction it.
  - now simpl.
  - simpl.  enough (` (get it n1) <= ` (get it n2)).
    + lia.
    + now apply IHit.
  - destruct n1 as [ n1k n1le ] in * |- *.  destruct n1k in * |- *.
    + simpl.  lia.
    + destruct n2 as [ n2k n2le ] in * |- *. inversion n1_le_n2 as [ inv_eq | inv_lt0 inv_lt1 inv_lt2 ].
      * simpl in inv_eq.  revert n1_le_n2.  revert n2le.  rewrite <- inv_eq.  intros n2le n1_le_n2.
        apply IHit.  simpl.  lia.
      * simpl in inv_lt1, inv_lt2.  revert n1_le_n2.  revert n2le.  rewrite <- inv_lt2.  intros n2le n1_le_n2.
        apply IHit.  simpl.  lia.
Qed.

Fixpoint compose {p q r} (this: t q r) (that: t p q) : t p r :=
  (fun f => f this) match that in t p q return t q r -> t p r with
    | nil => fun this => this
    | emit rest => fun this => (*emit (compose this rest*) _
    | skip rest => fun this => compose_skip this rest
  end
with compose_skip {p q r} (this : t (S q) r) : t p q -> t p r :=
  match this with
    | nil => fun _ => nil
    | emit rest => compose rest
    | skip rest => _ (* fun that => skip (compose_skip rest that) *)
  end.

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
*)

Program Instance Δ : Category := {|
  obj := nat;
  hom := Shuffle.t;
  homset x y := {| equiv := _; |};
  id x := _;
|}.
Next Obligation. (* id x *)
induction x.
- exact nil.
- apply emit.  now apply skip.
Defined.
Next Obligation.
*)