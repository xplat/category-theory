Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Functors map objects and morphisms between categories, where such mappings
   preserve equivalences and basic categorical structure (identity and
   composition). Note that there are many species of functor, one each for the
   various categorical structures (included below), for example, the
   `CartesianFunctor` that maps products to products and preserves all its
   structural properties and laws. *)

Class Functor {C D : Category} := {
  fobj : C -> D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_respects :> ∀ x y, Proper (equiv ==> equiv) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.

Declare Scope functor_scope.
Declare Scope functor_type_scope.
Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.

(* Functors used as functions map objects of categories, similar to the way
   type constructors behave in Haskell. We cannot, unfortunately, have a
   similar coercion for morphisms, because coercions cannot be bound to
   scopes. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

Arguments fmap
  {C%category D%category Functor%functor x%object y%object} f%morphism.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fobj[ F ]" := (@fobj _ _ F%functor)
  (at level 9, format "fobj[ F ]") : object_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 9, format "fmap[ F ]") : morphism_scope.

Hint Rewrite @fmap_id : categories.

Set Transparent Obligations.
Print eq_rect.

Lemma swap_eq_rect : ∀ A (x y : A) (P : A -> Type) (f : P x) (g : P y) (e : x = y) (r : ∀ {z}, P z -> P z -> Type),
  r (eq_rect x P f y e) g -> r f (eq_rect y P g x (eq_sym e)).
Proof.  intros * hyp.  destruct e.  now simpl in hyp |- *.  Qed.

Program Instance Functor_Setoid {C D : Category} : Setoid (C ⟶ D) := {
  equiv := fun F G =>
    { equ : ∀ x : C, F x = G x
    & ∀ (x y : C) (f : x ~> y),
        @eq_rect obj[D] (F x) (fun o => o ~> G y) (@eq_rect obj[D] (F y) (fun o => F x ~> o) (fmap[F] f) (G y) (equ y)) (G x) (equ x) ≈ fmap[G] f };
  setoid_equiv := {|
    Equivalence_Reflexive := ?[?refl];
    Equivalence_Symmetric := ?[?sym];
    Equivalence_Transitive := ?[?trans];
  |};
}.
Next Obligation.
intros F G [equ e].  unshelve esplit.
- easy.
- intros x y f.  specialize e with x y f.
  apply symmetry.
  remember (fmap[F] f) as Ff.
  remember (fmap[G] f) as Gf.
  clear HeqGf HeqFf.
  remember (fobj[F]) as oF.
  remember (fobj[G]) as oG.
  remember (equ x) as equx.
  remember (equ y) as equy.
  clear Heqequx Heqequy.
  remember (oF x) as Fx.
  remember (oF y) as Fy.
  remember (oG x) as Gx.
  remember (oG y) as Gy.
  destruct equx.
  destruct equy.
  now simpl in e |- *.
Qed.
Next Obligation.
intros F G H [FeqGo FeqGa] [GeqHo GeqHa].  unshelve esplit.
- intros x.  transitivity (G x); easy.
- intros x y f.  specialize FeqGa with x y f.  specialize GeqHa with x y f.
  simpl.
  remember (fmap[F] f) as Ff.  remember (fmap[G] f) as Gf.  remember (fmap[H] f) as Hf.
  clear HeqFf HeqGf HeqHf.
  remember (fobj[F]) as oF.  remember (fobj[G]) as oG.  remember (fobj[H]) as oH.
  remember (FeqGo x) as FeqGx.  remember (FeqGo y) as FeqGy.
  remember (GeqHo x) as GeqHx.  remember (GeqHo y) as GeqHy.
  clear HeqFeqGx HeqFeqGy HeqGeqHx HeqGeqHy.
  remember (oF x) as Fx.  remember (oG x) as Gx.  remember (oH x) as Hx.
  remember (oF y) as Fy.  remember (oG y) as Gy.  remember (oH y) as Hy.
  destruct FeqGx.  destruct GeqHx.  destruct FeqGy.  destruct GeqHy.
  simpl in FeqGa, GeqHa |- *.  now apply (transitivity (y := Gf)).
Qed.

Ltac constructive :=
  simpl;
  match goal with
    [ |- { iso : ?I & ?F } ] =>
    given (iso : I); [ intros; isomorphism; simpl; intros
                     | exists iso; intros ]
  end.

Program Instance fobj_iso `(F : C ⟶ D) :
  Proper (Isomorphism ==> Isomorphism) (fobj[F]).
Next Obligation.
  proper.
  refine {| to   := fmap[F] (to X)
          ; from := fmap (from X) |}.
    rewrite <- fmap_comp.
    rewrite iso_to_from; cat.
  rewrite <- fmap_comp.
  rewrite iso_from_to; cat.
Defined.

Instance fobj_respects `(F : C ⟶ D) :
  Proper (equiv ==> equiv) (@fobj C D F) := @fobj_iso C D F.

Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).

Program Definition Id {C : Category} : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Arguments Id {C} /.

Notation "Id[ C ]" := (@Id C) (at level 9, format "Id[ C ]") : functor_scope.

Program Definition Compose {C D E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. intros; rewrite !fmap_comp; reflexivity. Qed.

Hint Unfold Compose : core.

Notation "F ◯ G" := (Compose F%functor G%functor)
  (at level 40, left associativity) : category_scope.

Program Instance Compose_respects {C D E : Category} :
  Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
Next Obligation.
  simpl.  intros F G [FeqGo FeqGa].  simpl.  intros I J [IeqJo IeqJa].  simpl.  unshelve esplit.
  - intros x.  rewrite IeqJo.  now rewrite FeqGo.
  - intros x y f.  simpl.  specialize IeqJa with x y f.
    remember (fmap[I] f) as If.  remember (fmap[J] f) as Jf.  clear HeqIf HeqJf.
    remember (fobj[I]) as Io.  remember (fobj[J]) as Jo.
    remember (IeqJo x) as IeqJx.  remember (IeqJo y) as IeqJy.
    clear HeqIeqJx HeqIeqJy.
    remember (Io x) as Ix.  remember (Jo x) as Jx.
    remember (Io y) as Iy.  remember (Jo y) as Jy.
    destruct IeqJx.  destruct IeqJy.  unfold eq_ind_r.  simpl in IeqJa |- *.
    rewrite <- IeqJa.
    specialize FeqGa with Ix Iy If.
    remember (fmap[F] If) as FIf.  remember (fmap[G] If) as GIf.  clear HeqFIf HeqGIf.
    remember (fobj[F]) as Fo.  remember (fobj[G]) as Go.
    remember (FeqGo Ix) as FeqGIx.  remember (FeqGo Iy) as FeqGIy.
    clear HeqFeqGIx HeqFeqGIy.
    remember (Fo Ix) as FIx.  remember (Go Ix) as GIx.
    remember (Fo Iy) as FIy.  remember (Go Iy) as GIy.
    destruct FeqGIx.  destruct FeqGIy.
    now simpl.
Qed.

Corollary fobj_Compose `(F : D ⟶ E) `(G : C ⟶ D) {x} :
  fobj[F ◯ G] x = fobj[F] (fobj[G] x).
Proof. reflexivity. Defined.

Class Full `(F : C ⟶ D) := {
  prefmap {x y} (g : F x ~> F y) : x ~> y;

  prefmap_respects {x y} : Proper (equiv ==> equiv) (@prefmap x y);

  prefmap_id : ∀ x, @prefmap x x id ≈ id;
  prefmap_comp : ∀ x y z (f : F y ~> F z) (g : F x ~> F y),
    prefmap (f ∘ g) ≈ prefmap f ∘ prefmap g;

  fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g
}.

Class Faithful `(F : C ⟶ D) := {
  fmap_inj {x y} (f g : x ~> y) : fmap[F] f ≈ fmap[F] g -> f ≈ g
}.

(* Properties that follow from the above. *)
Lemma FullyFaithful `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F} :
  ∀ x y, F x ≅ F y -> x ≅ y.
Proof.
  intros.
  construct.
  + apply prefmap, X.
  + apply prefmap, X.
  + abstract
      (simpl;
       rewrite <- prefmap_comp;
       destruct H;
       rewrite iso_to_from;
       apply prefmap_id).
  + abstract
      (simpl;
       rewrite <- prefmap_comp;
       destruct H;
       rewrite iso_from_to;
       apply prefmap_id).
Defined.

Definition FAlgebra `(F : C ⟶ C) (a : C) := F a ~> a.

Definition FCoalgebra `(F : C ⟶ C) (a : C) := a ~> F a.

Definition FGDialgebra `(F : C ⟶ C) `(G : C ⟶ C) (a : C) := F a ~> G a.
