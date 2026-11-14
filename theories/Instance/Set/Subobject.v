From Cats Require Import Cat.Core.
From Cats Require Import Cat.Pullback.
From Cats Require Import Cat.Morphism.
From Cats Require Import Cat.Functor.Core.
From Cats Require Import Instance.Set.Core.



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

Program Canonical SubObjS Z
  : SetC
  :=
  {|carrier := Sub Z
  |}.

(** Pull back the displayed subobject along the base map.

<<
sX ------> sY
    v          v
    |          |
    |          s
    |          |
    v          v
    X ---f---> Y
>>
*)

(** 将 Y 的子对象 s 沿 f 拉回，得到 X 的子对象及其指向 s 的比较映射。 *)

Program Definition Sub_fmap {X Y : Ob}
    (f : Hom X Y) (sY : Sub Y)
  : Sub X
  :=
  {|sub := Pb f sY
  ; sub_mono :=
      {|mor := pb1 f sY
      |}
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

(** The chosen inverse-image subobject has the selected pullback as its
    domain. *)

(** 选定逆像子对象以指定拉回作为定义域。 *)

Proposition Sub_fmap_Ob {X Y} {f : Hom X Y} {r : Sub Y}
  : sub (Sub_fmap f r) = X ×[f,r] (sub r).
Proof. simpl. auto. Qed.

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
