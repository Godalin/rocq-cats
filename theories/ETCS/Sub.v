From Cats Require Import Cat.Core.
From Cats Require Import Cat.Pullback.
From Cats Require Import Cat.Morphism.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Set.



(** * Sub-object Functor *)

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
    rewrite pb_β1. cato.
    rewrite <- axiom_comp_assoc, <- Hrs.
    apply axiom_pb_cond.
  - exists (pb (pb1 f s) (sr ∘ pb2 f s)).
    simpl. unfold is_factored_through_by.
    rewrite pb_β1. cato.
    rewrite <- axiom_comp_assoc, <- Hsr.
    apply axiom_pb_cond.
Qed.
Next Obligation. intros f g Hfg s. simpl.
  apply iso_Sub_eq. simpl.
  exists (pb (Sub_fmap g s) (pb2 g s)).
  exists (pb (Sub_fmap f s) (pb2 f s)).
  simpl. repeat split.
  - rewrite pb_β1. cato. rewrite Hfg. cato.
  - rewrite pb_β1. cato. rewrite <- Hfg. cato.
  - admit.
  - admit.
Admitted.
Next Obligation.
  intros s. simpl. apply iso_Sub_eq. simpl.
  exists (pb s id). exists (pb2 id s).
  repeat split.
  - rewrite pb_β1. cato. cato. cato.
  - rewrite <- (axiom_id_l (pb1 _ _)). cato.
  - rewrite pb_β2; repeat cato.
  - admit.
Admitted.
Next Obligation.
  intros s. simpl. apply iso_Sub_eq. simpl.
Admitted.

End Sub.



(** * Sub-object Classifier *)
