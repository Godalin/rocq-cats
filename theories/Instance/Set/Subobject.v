From Cats Require Export Cat.Subobject.
From Cats Require Import
  Cat.Core
  Cat.Pullback
  Cat.Morphism
  Cat.Functor.Core
  Instance.Set.Core.



(** * Sub-object Functor

    The type of all sub-objects of a given object in a category is naturally
    equipped with a equivalence the [Sub_eq], in our setoid setting, this
    structure fits well as an contravariant functor. *)

(** * 子对象函子

    范畴中给定对象的子对象类型自然带有等价关系 [Sub_eq]；在广集基础下，该结构
    组成反变函子。 *)

Section Sub.
Context {C : Cat} `{H : !HasPullback C}.

(** The setoid of subobjects with mutual-factorization equality. *)

(** 以相互分解为相等的子对象广集。 *)

Program Canonical SubObjS (Z : C)
  : SetC
  :=
  {|carrier := Sub Z
  |}.

(** Subobject inverse image is a contravariant setoid-valued functor. *)

(** 子对象逆像是反变广集值函子。 *)

Program Canonical SubF
  : Fct (op C) SetCat
  :=
  {|F0 Z := SubObjS Z
  ; F1 Y X (f : (@Hom C) X Y) :=
      {|func := Sub_fmap f
      |}
  |}.
Next Obligation.
  intros r s [Hrs Hsr].
  split; apply sub_inverse_le; assumption.
Qed.
Next Obligation.
  intros f g Hfg s. change ((@Hom C) Y X) in f, g. simpl. split.
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
  change ((@Hom C) Z Y) in f. change ((@Hom C) Y X) in g.
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
