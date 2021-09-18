Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Construction.Comma.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Wikipedia: "If the domains of S, T are equal, then the diagram which
   defines morphisms in S↓T with α=β, α′=β′, g=h is identical to the diagram
   which defines a natural transformation S ⟹ T. The difference between the
   two notions is that a natural transformation is a particular collection of
   morphisms of type of the form S(α) → T(α), while objects of the comma
   category contains all morphisms of type of such form. A functor to the
   comma category selects that particular collection of morphisms. This is
   described succinctly by an observation by Huq that a natural transformation
   η : S → T, with S, T : A → C, corresponds to a functor A → (S↓T) which maps
   each object α to (α, α, η α) and maps each morphism g to (g, g). This is a
   bijective correspondence between natural transformations S ⟹ T and functors
   A ⟶ (S↓T) which are sections of both forgetful functors from S↓T."

   This is also given in Mac Lane, page 47, exercise 4. *)

Program Definition Comma_Functor {C D : Category} {S T : D ⟶ C}
        (F : S ⟹ T) : D ⟶ (S ↓ T) := {|
  fobj := fun X : D => ((X, X); F X);
  fmap := fun _ _ f => ((f, f); _)
|}.
Next Obligation. apply naturality_sym. Qed.

Local Obligation Tactic := simpl; intros.

Program Definition Comma_Transform {C D : Category} {S T : D ⟶ C}
        (F : D ⟶ (S ↓ T))
        (proj1 : comma_proj1 ◯ F ≈[Cat] Id)
        (proj2 : comma_proj2 ◯ F ≈[Cat] Id) : S ⟹ T := {|
  transform := fun X => `2 (F X)
|}.
Next Obligation.
  now rewrite (`1 proj1 X).
Defined.
Next Obligation.
  now rewrite (`1 proj2 X).
Defined.
Next Obligation.
  unfold Comma_Transform_obligation_1, Comma_Transform_obligation_2, eq_ind_r.
  simpl.
  destruct proj1 as [proj1o proj1a].
  destruct proj2 as [proj2o proj2a].
  simpl.
  specialize proj1a with x y f.  specialize proj2a with x y f.
  remember (proj1o x) as proj1x.  clear Heqproj1x.
  remember (proj2o x) as proj2x.  clear Heqproj2x.
  remember (proj1o y) as proj1y.  clear Heqproj1y.
  remember (proj2o y) as proj2y.  clear Heqproj2y.
  remember (fmap[F] f) as Ff.  destruct Ff as [[hFf tFf] eFf].  clear HeqFf.
  remember (F x) as Fx.
  remember (F y) as Fy.
  destruct Fx as [[hFx tFx] aFx].  simpl in * |- *.
  destruct proj1x, proj2x.  simpl in * |- *.
  destruct Fy as [[hFy tFy] aFy].  simpl in * |- *.
  destruct proj1y, proj2y.  simpl in * |- *.
  rewrite proj1a, proj2a in eFf.  now rewrite eFf.
Qed.
Next Obligation.
  unfold Comma_Transform_obligation_1, Comma_Transform_obligation_2, eq_ind_r.
  simpl.
  destruct proj1 as [proj1o proj1a].
  destruct proj2 as [proj2o proj2a].
  simpl.
  specialize proj1a with x y f.  specialize proj2a with x y f.
  remember (proj1o x) as proj1x.  clear Heqproj1x.
  remember (proj2o x) as proj2x.  clear Heqproj2x.
  remember (proj1o y) as proj1y.  clear Heqproj1y.
  remember (proj2o y) as proj2y.  clear Heqproj2y.
  remember (fmap[F] f) as Ff.  destruct Ff as [[hFf tFf] eFf].  clear HeqFf.
  remember (F x) as Fx.
  remember (F y) as Fy.
  destruct Fx as [[hFx tFx] aFx].  simpl in * |- *.
  destruct proj1x, proj2x.  simpl in * |- *.
  destruct Fy as [[hFy tFy] aFy].  simpl in * |- *.
  destruct proj1y, proj2y.  simpl in * |- *.
  rewrite proj1a, proj2a in eFf.  now rewrite eFf.
Qed.