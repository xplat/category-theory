Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Export Category.Lib.Foundation.
Require Export Coq.Classes.CEquivalence.
Require Export Coq.Classes.CRelationClasses.
Require Export Coq.Classes.CMorphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.

Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.
Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity) : category_theory_scope.
Notation "¬ x" := (~x)
  (at level 75, right associativity) : category_theory_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.

Notation "P ∨ Q" := ({ P } + { Q })
  (at level 85, right associativity) : category_theory_scope.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity) :
  category_theory_scope.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :> Equivalence equiv
}.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

Program Instance setoid_refl `(sa : Setoid A) :
  Reflexive equiv.
Obligation 1. apply setoid_equiv. Qed.

Program Instance setoid_sym `(sa : Setoid A) :
  Symmetric equiv.
Obligation 1. apply setoid_equiv; auto. Qed.

Program Instance setoid_trans `(sa : Setoid A) :
  Transitive equiv.
Obligation 1.
  apply setoid_equiv.
  destruct sa; simpl in *.
  destruct setoid_equiv0.
  eapply Equivalence_Transitive; eauto.
Qed.

Delimit Scope signature_scope with signature.

Notation "f ++> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f ==> g" := (respectful f g)%signature
  (right associativity, at level 55) : signature_scope.
Notation "f --> g" := (respectful (Basics.flip f) g)%signature
  (right associativity, at level 55) : signature_scope.

Arguments Proper {A}%type R%signature m.
Arguments respectful {A B}%type (R R')%signature _ _.
