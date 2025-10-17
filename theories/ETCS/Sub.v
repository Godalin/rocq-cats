From Cats Require Import Cat.Core.
From Cats Require Import Cat.Pullback.
From Cats Require Import Cat.Morphism.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Set.



(** * Sub-object Functor

    The type of all sub-objects of a given object in a category
    is naturally equipped with a equivalence the [Sub_eq], in our
    setoid setting, this structure fits well as an contravariant
    functor. *)

Section Sub.
Context `{C : Cat} `{H : !HasPullback C}.

Program Canonical Structure SubObject Z : SetC :=
  {|carrier := Sub Z
  ; carrier_equiv := Sub_eq Z
  |}.
Next Obligation. apply Sub_eq_Equivalence. Qed.

(** sX ------> sY
    v          v
    |          |
    |          s
    |          |
    v          v
    X ---f---> Y *)

Program Definition Sub_fmap {X Y : Ob}
    (f : Hom X Y) (sY : Sub Y) : Sub X :=
  {|sub := Pb f sY
  ; sub_mono := {| mor := pb1 f sY |}
  |}.
Next Obligation.
  intros W x y H1.
  assert (Hx : f ∘ (pb1 f sY ∘ x) ≈ sY ∘ (pb2 f sY ∘ x)).
  { rewrite <- axiom_comp_assoc.
    rewrite <- axiom_comp_assoc.
    rewrite axiom_pb_cond. cato. }
  assert (Hy : f ∘ (pb1 f sY ∘ y) ≈ sY ∘ (pb2 f sY ∘ y)).
  { rewrite <- axiom_comp_assoc.
    rewrite <- axiom_comp_assoc.
    rewrite axiom_pb_cond. cato. }
  destruct (axiom_pb_unique Hx) as [[Hx11 Hx12] Hx2].
  specialize (Hx2 y).
  assert (Hxη : x ≈ pb (pb1 f sY ∘ x) (pb2 f sY ∘ x)).
  { apply pb_η. auto. split; cato. }
  assert (Hyη : y ≈ pb (pb1 f sY ∘ y) (pb2 f sY ∘ y)).
  { apply pb_η. auto. split; cato. }
  rewrite <- Hxη in Hx2.
  symmetry. apply Hx2.
  split. symmetry. auto.
  assert (sY ∘ (pb2 f sY ∘ x) ≈ sY ∘ (pb2 f sY ∘ y)).
  { rewrite <- Hx, <- Hy. apply comp_l. auto. }
  apply sub_mono in H0. symmetry. auto.
Qed.

Proposition Sub_fmap_Ob {X Y} {f : Hom X Y} {r : Sub Y}
  : sub (Sub_fmap f r) = X ×[f,r] (sub r).
Proof. simpl. auto. Qed.

Program Canonical Structure SubF : Functor (op C) SetCat :=
  {|F0 Z := SubObject Z
  ; F1 Y X f := {| func := Sub_fmap f |}
  |}.
Next Obligation. intros r s [[rs Hrs] [sr Hsr]].
  split. unfold is_factored_through_by in *.
  - exists (pb (pb1 f r) (rs ∘ pb2 f r)).
    simpl. unfold is_factored_through_by.
    carw.
    rewrite <- axiom_comp_assoc, <- Hrs. cato.
  - exists (pb (pb1 f s) (sr ∘ pb2 f s)).
    simpl. unfold is_factored_through_by.
    carw.
    rewrite <- axiom_comp_assoc, <- Hsr. cato.
Qed.
Next Obligation. intros f g Hfg s. simpl.
  apply iso_Sub_eq. simpl.
  exists (pb (Sub_fmap g s) (pb2 g s)).
  exists (pb (Sub_fmap f s) (pb2 f s)).
  simpl. repeat split.
  - carw. rewrite Hfg. cato.
  - carw. rewrite <- Hfg. cato.
  - assert (id ≈ pb (pb1 g s) (pb2 g s)).
    apply pb_η. cato. split; cato.
    rewrite H0. apply pb_η. cato. split.
    rewrite <- axiom_comp_assoc. carw.
    rewrite Hfg. cato. rewrite <- Hfg. cato.
    rewrite <- axiom_comp_assoc. carw.
    rewrite Hfg. cato. rewrite <- Hfg. cato.
  - assert (id ≈ pb (pb1 f s) (pb2 f s)).
    apply pb_η. cato. split; cato.
    rewrite H0. apply pb_η. cato. split.
    rewrite <- axiom_comp_assoc. carw.
    rewrite <- Hfg. cato. rewrite Hfg. cato.
    rewrite <- axiom_comp_assoc. carw.
    rewrite <- Hfg. cato. rewrite Hfg. cato.
Qed.
Next Obligation.
  intros s. simpl. apply iso_Sub_eq. simpl.
  exists (pb s id). exists (pb2 id s).
  repeat split.
  - carw.
  - rewrite <- (axiom_id_l (pb1 _ _)). cato.
  - carw.
  - assert (id ≈ pb (pb1 id s) (pb2 id s)).
    apply pb_η. cato. cato. rewrite H0.
    apply pb_η. cato. split.
    rewrite <- axiom_comp_assoc, pb_β1.
    rewrite <- (axiom_id_l (pb1 _ _ )).
    symmetry. cato. carw.
    rewrite <- axiom_comp_assoc. carw.
Qed.
Next Obligation.
  intros s. simpl. apply iso_Sub_eq. simpl.
  exists (pb #pb1 (#pb2 ∘ #pb2)).
  epose (h := pb (f ∘ #pb1) #pb2).
  exists (pb #pb1 h). unfold h.
  repeat split.
  - carw. cacr. rewrite axiom_pb_cond.
    cacl. cacl. rewrite axiom_pb_cond. cato.
  - carw. rewrite <- axiom_pb_cond. cacr.
  - eassert (id ≈ pb _ _).
    apply pb_η. apply axiom_pb_cond. carw.
    split; cato. rewrite H0.
    apply pb_η. cato. split; cacl; carw.
    cacr. rewrite axiom_pb_cond. cacl.
    rewrite axiom_pb_cond. cacr.
    carw. rewrite <- axiom_pb_cond. cacl.
    (* rewrite <- pb_η.
    eassert (_ ∘ #pb1 ∘ pb (pb1 f (pb1 g s)) ((pb2 g s) ∘ (pb2 f (pb1 g s))) ≈ (pb2 f (pb1 g s))).
    { cacr. carw. apply axiom_pb_cond. } *)
    admit.
    carw. cacl.
  - eassert (id ≈ pb _ _).
    apply pb_η. apply axiom_pb_cond. carw.
    split; cato. rewrite H0.
    apply pb_η. cato. split; cacl; carw.
    cacl. cacl.
    rewrite <- axiom_pb_cond. cacr.
    rewrite axiom_pb_cond. cacr.
    admit.
    cacl. rewrite <- axiom_pb_cond. cacr.
    rewrite axiom_pb_cond. cacl.
Admitted.

End Sub.



(** * Sub-object Classifier *)
