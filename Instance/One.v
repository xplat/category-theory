Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Terminal.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition _1 : Category := {|
  obj     := unit;
  hom     := fun _ _ => unit;
  homset  := Morphism_equality;
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
|}.

Notation "1" := _1 : category_scope.

Notation "one[ C ]" := (@one Cat _ C)
  (at level 9, format "one[ C ]") : object_scope.

Program Instance Erase `(C : Category) : C ⟶ 1 := {
  fobj := fun _ => ();
  fmap := fun _ _ _ => id
}.

Program Instance Cat_Terminal : @Terminal Cat := {
  terminal_obj := _1;
  one := Erase
}.
Next Obligation.
  unshelve esplit.
  - intros v.  now destruct (f v), (g v).
  - intros vx vy vf.  simpl.
    destruct (f vx), (g vx), (f vy), (g vy).  simpl.
    now destruct (fmap[f] vf), (fmap[g] vf).
Qed.
