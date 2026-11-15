From Cats Require Import
  Instance.Set.PresheafRegionUnion
  Cat.Morphism.

(** * Independent Membership and Equality Sizes *)

(** * 独立的隶属及相等大小 *)

(** The constant membership type may be empty or have distinct witnesses;
    restriction retains exactly the supplied witness. *)

(** 常值隶属类型可以为空或含不同见证；限制恰好保留给定见证。 *)

Program Definition ConstantRegion {C : Cat} (Q : Fct (C^op) SetCat)
    (W : Type)
  : PresheafRegion Q
  :=
  {|region_member X x := W
  ; region_precomp X Y f x H := H
  |}.
Next Obligation. intros x y E. split; exact (λ w, w). Defined.

(** ** Equality Above Values

    The category objects and homs are larger than the value carrier.
    The two membership types lie at distinct smaller levels. Equality
    is larger than the value carrier and smaller than category data. *)

(** ** 相等高于取值

    范畴对象与态射大于取值载体；两个隶属类型处于严格不同的较小层级。
    相等大于取值载体而小于范畴数据。 *)

Section HigherEquality.
Universes l r s u p h o.
Constraint l < r, r < s, s < u, u < p, p < h, h < o.
Context {C : Cat@{o h l _ _}}
    {Q P : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    (W : Type@{r}) (V : Type@{s}).
Let R := ConstantRegion Q W.
Let S := ConstantRegion Q V.
Context (a : RegionPsh R ⇒ P) (b : RegionPsh S ⇒ P)
    (H : (a ∘Nv RegionInterLeftN R S) ≈N (b ∘Nv RegionInterRightN R S)).

(** The stage carrier keeps both membership universes below its bound. *)

(** 阶段载体将两个隶属宇宙容纳在其界内。 *)

Definition high_union
  : Fct (C^op) SetCat@{u p _ _ _ _ _}
  := RegionPsh (RegionUnion R S).

Definition high_glue
  : high_union ⇒ P
  := RegionUnionGluingN R S a b H.

Definition high_left
  : (high_glue ∘Nv RegionUnionLeftN R S) ≈N a
  := region_union_gluing_β1 R S a b H.

Definition high_right
  : (high_glue ∘Nv RegionUnionRightN R S) ≈N b
  := region_union_gluing_β2 R S a b H.

Definition high_pushout
  : is_pushout (C := FctCat (C^op) SetCat@{u p _ _ _ _ _})
      (RegionInterLeftN R S) (RegionInterRightN R S)
      high_union (RegionUnionLeftN R S) (RegionUnionRightN R S)
  := region_union_pushout R S.

Definition high_mono
  : @is_mono (FctCat (C^op) SetCat@{u p _ _ _ _ _}) _ _ (RegionInclusionN R)
  := region_inclusion_mono R.

Definition high_factor (α : P ⇒ Q) (K : ∀ X (x : P X), W)
  : P ⇒ RegionPsh R
  := RegionFactorN R α K.

Definition high_factor_recovery (α : P ⇒ Q) (K : ∀ X (x : P X), W)
  : (RegionInclusionN R ∘Nv high_factor α K) ≈N α
  := region_factor_comm R α K.

(** Independent agreement witnesses do not enter mediator equality. *)

(** 独立的相容见证不进入中介相等。 *)

Definition high_glue_proper
    (a' : RegionPsh R ⇒ P) (b' : RegionPsh S ⇒ P)
    (K : (a' ∘Nv RegionInterLeftN R S) ≈N (b' ∘Nv RegionInterRightN R S))
    (E : a ≈N a') (F : b ≈N b')
  : high_glue ≈N RegionUnionGluingN R S a' b' K
  := region_union_gluing_proper R S a a' b b' H K E F.

End HigherEquality.

(** ** Equality Below Values

    Reverse the carrier/equality order and the order of the membership
    types, while keeping the generator-index category larger still. *)

(** ** 相等低于取值

    反转载体与相等以及两个隶属类型的次序；生成元索引范畴仍然更大。 *)

Section LowerEquality.
Universes l r s p u h o.
Constraint l < r, r < p, p < s, s < u, u < h, h < o.
Context {C : Cat@{o h l _ _}}
    {Q P : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    (W : Type@{s}) (V : Type@{r}).
Let R := ConstantRegion Q W.
Let S := ConstantRegion Q V.
Context (a : RegionPsh R ⇒ P) (b : RegionPsh S ⇒ P)
    (H : (a ∘Nv RegionInterLeftN R S) ≈N (b ∘Nv RegionInterRightN R S)).

Definition low_union
  : Fct (C^op) SetCat@{u p _ _ _ _ _}
  := RegionPsh (RegionUnion R S).

Definition low_glue
  : low_union ⇒ P
  := RegionUnionGluingN R S a b H.

Definition low_left
  : (low_glue ∘Nv RegionUnionLeftN R S) ≈N a
  := region_union_gluing_β1 R S a b H.

Definition low_right
  : (low_glue ∘Nv RegionUnionRightN R S) ≈N b
  := region_union_gluing_β2 R S a b H.

Definition low_pushout
  : is_pushout (C := FctCat (C^op) SetCat@{u p _ _ _ _ _})
      (RegionInterLeftN R S) (RegionInterRightN R S)
      low_union (RegionUnionLeftN R S) (RegionUnionRightN R S)
  := region_union_pushout R S.

Definition low_mono
  : @is_mono (FctCat (C^op) SetCat@{u p _ _ _ _ _}) _ _ (RegionInclusionN R)
  := region_inclusion_mono R.

Definition low_factor (α : P ⇒ Q) (K : ∀ X (x : P X), W)
  : P ⇒ RegionPsh R
  := RegionFactorN R α K.

Definition low_factor_recovery (α : P ⇒ Q) (K : ∀ X (x : P X), W)
  : (RegionInclusionN R ∘Nv low_factor α K) ≈N α
  := region_factor_comm R α K.

(** Independent agreement witnesses do not enter mediator equality. *)

(** 独立的相容见证不进入中介相等。 *)

Definition low_glue_proper
    (a' : RegionPsh R ⇒ P) (b' : RegionPsh S ⇒ P)
    (K : (a' ∘Nv RegionInterLeftN R S) ≈N (b' ∘Nv RegionInterRightN R S))
    (E : a ≈N a') (F : b ≈N b')
  : low_glue ≈N RegionUnionGluingN R S a' b' K
  := region_union_gluing_proper R S a a' b b' H K E F.

End LowerEquality.
