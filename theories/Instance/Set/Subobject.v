From Cats Require Import Cat.Core.
From Cats Require Import Cat.Pullback.
From Cats Require Import Cat.Morphism.
From Cats Require Import Cat.Functor.
From Cats Require Import Instance.Set.Core.



(** * Sub-object Functor

    The type of all sub-objects of a given object in a category
    is naturally equipped with a equivalence the [Sub_eq], in our
    setoid setting, this structure fits well as an contravariant
    functor. *)

Section Sub.
Context `{C : Cat} `{H : !HasPullback C}.

Program Canonical SubObject Z : SetC :=
  {|carrier := Sub Z |}.

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
  { rewrite <- comp_assoc.
    rewrite <- comp_assoc.
    rewrite pullback_comm. cato. }
  assert (Hy : f ∘ (pb1 f sY ∘ y) ≈ sY ∘ (pb2 f sY ∘ y)).
  { rewrite <- comp_assoc.
    rewrite <- comp_assoc.
    rewrite pullback_comm. cato. }
  destruct (pullback_mediator_unique Hx) as [[Hx11 Hx12] Hx2].
  specialize (Hx2 y).
  assert (Hxη : x ≈ pb (pb1 f sY ∘ x) (pb2 f sY ∘ x) Hx).
  { apply pb_η. split; cato. }
  assert (Hyη : y ≈ pb (pb1 f sY ∘ y) (pb2 f sY ∘ y) Hy).
  { apply pb_η. split; cato. }
  rewrite <- Hxη in Hx2.
  symmetry. apply Hx2.
  split. symmetry. auto.
  assert (sY ∘ (pb2 f sY ∘ x) ≈ sY ∘ (pb2 f sY ∘ y)).
  { rewrite <- Hx, <- Hy. apply comp_l. auto. }
  apply sub_mono in X0. symmetry. auto.
Qed.

Proposition Sub_fmap_Ob {X Y} {f : Hom X Y} {r : Sub Y}
  : sub (Sub_fmap f r) = X ×[f,r] (sub r).
Proof. simpl. auto. Qed.

Program Canonical SubF : Functor (op C) SetCat :=
  {|F0 Z := SubObject Z
  ; F1 Y X f := {| func := Sub_fmap f |}
  |}.
Next Obligation. intros r s [[rs Hrs] [sr Hsr]].
  split.
  - assert (Hcone : f ∘ pb1 f r ≈ s ∘ (rs ∘ pb2 f r)).
    { rewrite <- comp_assoc, <- Hrs. apply pullback_comm. }
    exists (pb (pb1 f r) (rs ∘ pb2 f r) Hcone).
    simpl. symmetry. apply pb_β1.
  - assert (Hcone : f ∘ pb1 f s ≈ r ∘ (sr ∘ pb2 f s)).
    { rewrite <- comp_assoc, <- Hsr. apply pullback_comm. }
    exists (pb (pb1 f s) (sr ∘ pb2 f s) Hcone).
    simpl. symmetry. apply pb_β1.
Qed.
Next Obligation. intros f g Hfg s. simpl. split.
  - assert (Hcone : g ∘ Sub_fmap f s ≈ s ∘ pb2 f s).
    { simpl. rewrite <- Hfg. apply pullback_comm. }
    exists (pb (Sub_fmap f s) (pb2 f s) Hcone).
    simpl. symmetry. apply pb_β1.
  - assert (Hcone : f ∘ Sub_fmap g s ≈ s ∘ pb2 g s).
    { simpl. rewrite Hfg. apply pullback_comm. }
    exists (pb (Sub_fmap g s) (pb2 g s) Hcone).
    simpl. symmetry. apply pb_β1.
Qed.
Next Obligation.
  intros s. simpl. split.
  exists (pb2 id s). simpl.
  rewrite <- (comp_id_l (pb1 _ _)). cato.
  assert (Hcone : id ∘ s ≈ s ∘ id). { carw. }
  exists (pb s id Hcone). simpl. symmetry. apply pb_β1.
Qed.
Next Obligation.
  intros s. simpl. split.
  - assert (Hinner : g ∘ (f ∘ pb1 (g ∘ f) s) ≈ s ∘ pb2 (g ∘ f) s).
    { rewrite <- comp_assoc. apply pullback_comm. }
    pose (inner := pb (f ∘ pb1 (g ∘ f) s) (pb2 (g ∘ f) s) Hinner).
    assert (Houter : f ∘ pb1 (g ∘ f) s ≈ pb1 g s ∘ inner).
    { symmetry. apply pb_β1. }
    exists (pb (pb1 (g ∘ f) s) inner Houter).
    simpl. symmetry. apply pb_β1.
  - assert (Hcone : (g ∘ f) ∘ pb1 f (pb1 g s)
        ≈ s ∘ (pb2 g s ∘ pb2 f (pb1 g s))).
    { rewrite comp_assoc, pullback_comm.
      rewrite <- comp_assoc, pullback_comm, comp_assoc.
      reflexivity. }
    exists (pb (pb1 f (pb1 g s)) (pb2 g s ∘ pb2 f (pb1 g s)) Hcone).
    simpl. symmetry. apply pb_β1.
Qed.

End Sub.
