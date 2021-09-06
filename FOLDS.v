Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".
Set Warnings "-unexpected-implicit-declaration".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition HomAddDependentSort `(C : Category) (arity: C ⟶ Sets) (x y: option C) :=
  match x with
    | None => match y with
        | None => unit
        | Some d => arity d
      end
    | Some c => match y with
        | None => Empty_set
        | Some d => c ~> d
      end
  end.

Ltac destruct_dependent_sort := match goal with
  | [ |- context[HomAddDependentSort _ _ ?X] ] =>
    lazymatch X with
      | Some _ => fail
      | None => fail
      | _ => idtac "boo" X; destruct X
    end
  | [ |- context[HomAddDependentSort _ _ _ ?X] ] =>
    lazymatch X with
      | Some _ => fail
      | None => fail
      | _ => idtac "hiss" X; destruct X
    end
  | [ H: context[HomAddDependentSort _ _ ?X ] |- _] =>
    lazymatch X with
      | Some _ => fail
      | None => fail
      | _ => idtac "buu" X; destruct X
    end
  | [ H: context[HomAddDependentSort _ _ _ ?X ] |- _] =>
    lazymatch X with
      | Some _ => fail
      | None => fail
      | _ => idtac "hyss" X; destruct X
    end
end.

Hint Extern 1 (HomAddDependentSort _ _ _ _) => destruct_dependent_sort : core.
Hint Extern 3 => destruct_dependent_sort : core.

Global Program Instance HomAddDependentSort_Setoid `(C : Category) (arity: C ⟶ Sets) (x y: option C)
  : Setoid (HomAddDependentSort C arity x y) := {|
  equiv := match x with
    | None => match y with
        | None => fun _ _ => unit
        | Some d => @equiv _ (arity d)
      end
    | Some c => match y with
        | None => fun _ _ => unit
        | Some d => @equiv _ (homset c d)
      end
  end
|}.

Next Obligation.
  equivalence. now repeat destruct_dependent_sort.
Qed.

(* automate away all the trivial cases *)
Program Definition AddDependentSort_compose `(C : Category) (arity: C ⟶ Sets) (x y z : option C)
  (f : HomAddDependentSort C arity y z) (g : HomAddDependentSort C arity x y) : HomAddDependentSort C arity x z := _.
Next Obligation.
  destruct x, y, z; try easy.
  - exact (f ∘ g).
  - exact (fmap[arity] f g).
Defined.

Program Definition AddDependentSort `(C : Category) (arity: C ⟶ Sets) : Category := {|
  obj := option obj[C];
  hom := HomAddDependentSort C arity;
  homset := HomAddDependentSort_Setoid C arity;
  id x := match x with | None => () | Some c => id end;
  compose := AddDependentSort_compose C arity;
  |}.

Next Obligation.
  intros f0 f1 f0_eq_f1 g0 g1 g0_eq_g1.
  repeat destruct_dependent_sort; try rewrite f0_eq_f1, g0_eq_g1; try easy; simpl.
  transitivity (fmap[arity] f0 g1).
  - now apply (proper_morphism).
  - apply (fun k => k g1). now apply (fmap_respects (Functor := arity)).
Qed.

Next Obligation.
  repeat destruct_dependent_sort; simpl; now try first [ apply id_left | apply (fmap_id (Functor := arity) f) ].
Qed.

Next Obligation.
  repeat destruct_dependent_sort; solve [apply id_right | easy].
Qed.

Next Obligation.
  repeat destruct_dependent_sort; try first [easy | apply comp_assoc].
  symmetry.
  apply (fmap_comp (Functor := arity) f g h).
Qed.

Next Obligation.
  repeat destruct_dependent_sort; try first [easy | apply comp_assoc_sym].
  apply (fmap_comp (Functor := arity) f g h).
Qed.

(*
(* Michael Makkai's FOLDS.  Sort of.  'Simple Categories' and DSVs are kinda
   nasty from a category theory perspective, so I am using categories
   of contexts instead, and building them up one sort or relation at a time
   using constructs similar to the ones Makkai uses to build his
   'generalized sketches'. *)

Record CtxAddDependentVariables `(C: Category) (arity: C) : Type := {
  base :> C ; (* The context with all variables of the old kinds/sortcons *)
  names : Type ; (* Names for the variables of the new sortcon *)
  args : names -> (base ~> arity) ; (* Substitutions giving the arguments to the sortcon for each variable *)
}.

Arguments names {_ _} _.
Arguments args {_ _} _ _.

Record SbsAddDependentVariables `{C: Category} {arity: C} (from to: CtxAddDependentVariables C arity) : Type := {
  sbase :> from ~> to ; (* substitution for other sortcons *)
  snames : names to -> names from ; (* how the new sortcon obligations get fulfilled *)
  sargs : ∀ name : names to, args from (snames name) ≈ args to name ∘ sbase ; (* check of sort consistency *)
}.

Arguments sbase {_ _ _ _} _.
Arguments snames {_ _ _ _} _ _.
Arguments sargs {_ _ _ _} _ _.

Global Program Instance SbsAddDependentVariables_Setoid
    `{C : Category} {arity: C} (from to: CtxAddDependentVariables C arity)
  : Setoid (SbsAddDependentVariables from to) := {|
  equiv := fun f g => { _: sbase f ≈ sbase g & ∀ name : names to, snames f name = snames g name }
|}.

Next Obligation.
  equivalence.
  rewrite e0, e.
  reflexivity.
Qed.

Program Definition AddDependentSort `(C: Category) (arity: C) : Category := {|
  obj := CtxAddDependentVariables C arity ;
  hom := SbsAddDependentVariables ;
  homset := SbsAddDependentVariables_Setoid ;
  id := fun x => {| sbase := id ; snames := fun name => name ; |} ;
  compose := fun x y z f g => {| sbase := sbase f ∘[C] sbase g ; snames := snames g \o snames f ; |} ;
|}.

Next Obligation.
  rewrite (sargs g), (sargs f), comp_assoc.
  reflexivity.
Qed.

Next Obligation.
  proper.
  rewrite e0, e.
  reflexivity.
Qed.
*)