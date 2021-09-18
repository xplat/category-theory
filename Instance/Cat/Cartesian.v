Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance Cat_Cartesian : @Cartesian Cat := {
  product_obj := @Product;
  fork := fun _ _ _ F G =>
            {| fobj := fun x => (F x, G x)
             ; fmap := fun _ _ f => (fmap[F] f, fmap[G] f) |};
  exl := fun _ _ =>
            {| fobj := fst
             ; fmap := fun _ _ => fst |};
  exr := fun _ _ =>
            {| fobj := snd
             ; fmap := fun _ _ => snd |};
}.
Next Obligation. proper; apply fmap_respects; auto. Qed.
Next Obligation. simplify; rewrite !fmap_comp; intuition. Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  intros F G [FeqGo FeqGa] I J [IeqJo IeqJa].
  simpl. unshelve esplit.
  - intros x.  now rewrite !FeqGo, !IeqJo.
  - intros x y f.
    specialize FeqGa with x y f.  specialize IeqJa with x y f.
    simpl.
    remember (FeqGo x) as FeqGx.  remember (FeqGo y) as FeqGy.
    remember (IeqJo x) as IeqJx.  remember (IeqJo y) as IeqJy.
    clear HeqFeqGx HeqFeqGy HeqIeqJx HeqIeqJy.
    remember (fmap[F] f) as Ff.  clear HeqFf.  remember (F x) as Fx.  remember (F y) as Fy.
    remember (fmap[G] f) as Gf.  clear HeqGf.  remember (G x) as Gx.  remember (G y) as Gy.
    remember (fmap[I] f) as If.  clear HeqIf.  remember (I x) as Ix.  remember (I y) as Iy.
    remember (fmap[J] f) as Jf.  clear HeqJf.  remember (J x) as Jx.  remember (J y) as Jy.
    destruct FeqGx, FeqGy, IeqJx, IeqJy.  simpl in FeqGa, IeqJa |- *.  easy.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  rename f into F.
  rename g into G.
  rename h into K.
  split; intros [KeqFGo KeqFGa].
  - simpl.  split; unshelve esplit.
    + intros x.  rewrite !KeqFGo.  simpl.  easy.
    + intros x.  rewrite !KeqFGo.  simpl.  easy.
    + intros x y f.  specialize KeqFGa with x y f.  unfold eq_ind_r.  simpl in KeqFGa |- *.
      remember (KeqFGo x) as KeqFGx.  remember (KeqFGo y) as KeqFGy.
      clear HeqKeqFGx HeqKeqFGy.
      remember (fmap[F] f) as Ff.  clear HeqFf.  remember (F x) as Fx.  remember (F y) as Fy.
      remember (fmap[G] f) as Gf.  clear HeqGf.  remember (G x) as Gx.  remember (G y) as Gy.
      remember (fmap[K] f) as Kf.  clear HeqKf.  remember (K x) as Kx.  remember (K y) as Ky.
      destruct Kf as [Kf1 Kf2].  destruct Kx as [Kx1 Kx2].  destruct Ky as [Ky1 Ky2].
      destruct KeqFGa as [KeqFGa1 KeqFGa2].
      simpl in * |- *.

(* i am
     _              _
 ___| |_ _   _  ___| | __
/ __| __| | | |/ __| |/ /
\__ \ |_| |_| | (__|   <
|___/\__|\__,_|\___|_|\_\ -jcd

*)

      destruct KeqFGx.
        remember (fst Kx) as Kx1.  remember (fst Ky) as Ky1.
       remember ( (Fy,Gy) ) as FGy.
      destruct KeqFGy.
    isomorphism.
    + exact (fst (to (x x0))).
    + exact (fst (from (x x0))).
    + exact (fst (iso_to_from (x x0))).
    + exact (fst (iso_from_to (x x0))).
  - apply (fst (e _ _ _)).
  - isomorphism.
    + exact (snd (to (x x0))).
    + exact (snd (from (x x0))).
    + exact (snd (iso_to_from (x x0))).
    + exact (snd (iso_from_to (x x0))).
  - apply (snd (e _ _ _)).
  - isomorphism.
    + exact(to (x0 x1), to (x x1)).
    + exact(from (x0 x1), from (x x1)).
    + exact(iso_to_from (x0 x1), iso_to_from (x x1)).
    + exact(iso_from_to (x0 x1), iso_from_to (x x1)).
  - apply e0.
  - apply e.
Qed.
