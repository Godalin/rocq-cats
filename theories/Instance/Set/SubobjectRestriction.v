From Cats Require Import
  Cat.Core
  Cat.Morphism
  Cat.Pullback
  Cat.SubobjectIntersection
  Instance.Set.Subobject
  Instance.Set.SubobjectIntersection.

(** * Restriction Along a Subobject

    Intersection uses the same pullback as inverse image along its first
    subobject. Reuse the existing factor correspondence to restrict an
    inclusion, retaining the actual maps in both directions. *)

(** * 沿子对象的限制

    交与沿第一个子对象的逆像使用同一拉回。复用已有分解对应来限制包含关系，
    保留两个方向上的实际映射。 *)

(** Inclusion of an intersection is inclusion after restriction to the
    first subobject. No terminal object or classifier is required. *)

(** 交的包含等价于限制到第一个子对象后的包含；不要求终对象或分类子。 *)

Definition sub_inverse_restriction {C : Cat} `{PB : !HasPullback C}
    {X : C} (r s t : Sub X)
  : r ∩Sub s ≲Sub t ↔ Sub_fmap r s ≲Sub Sub_fmap r t.
Proof.
  pose (U := sub_inverse_factor r (Sub_fmap r s) t). split.
  - intros H. exact (snd U H).
  - intros H. exact (fst U H).
Defined.
