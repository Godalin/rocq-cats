From Cats Require Export
  Cat.Monoidal.Associator
  Cat.Monoidal.Unitor
  Cat.Monoidal.Semigroupal.

Local Open Scope monoidal_scope.

(** * Premonoidal Categories

    Combine an independently chosen associator and unitors on the same
    tensor actions. Their triangle is the only additional compatibility
    condition; pentagon belongs to the associator characterization. *)

(** * 预幺半范畴

    在同一张量作用上组合独立选择的结合子和单位子。三角形是唯一新增相容条件；
    五边形属于结合子的刻画。 *)

(** ** Compatibility of Fixed Choices

    Fix the same named category and tensor for both packages. The triangle
    compares their existing maps without choosing a new one. *)

(** ** 固定选择的相容性

    为两份选择固定同一具名范畴及张量；三角形比较已有映射，不作新的选择。 *)

Minks.Mixin IsPremonoidal (C : Cat)
  extends HasTensorAssoc C, HasTensorUnitors C
  :=
  { tensor_triangle (X Y : C)
    : (X ⊲ λ[Y]) ∘ α[X; 𝐈; Y] ≈ ρ[X] ⊳ Y
  }.

Arguments tensor_triangle
  {C BC AC UC IP} _ _ : rename.

(** Add the associator and its coherent unitors to one binoidal tensor. *)

(** 为同一双侧张量加入结合子及相干单位子。 *)

Minks.Struct PremonoidalCat
  extends BinoidalCat
  with  associator : HasTensorAssoc,
        unitors : HasTensorUnitors,
        isPremonoidal : IsPremonoidal.
