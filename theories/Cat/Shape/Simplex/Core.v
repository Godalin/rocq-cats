From Cats Require Export
  Cat.Shape.Ordinal
  Cat.Functor.Core.
From Cats Require Import
  Cat.Core
  Cat.Natural
  Cat.CatCat
  Cat.Induced.

(** * The Simplex Category

    Objects are dimensions n, representing the nonempty ordinal [Ord n].
    Arrows are functors of those orders, hence monotone maps. Their specified
    equality is natural isomorphism, which here is equivalent to pointwise
    equality of finite positions. All category laws are inherited. *)

(** * 单纯范畴

    对象是维数 n，代表非空有限序数 [Ord n]。箭头是这些顺序间的函子，即保序
    映射，指定相等为自然同构；在这里它等价于有限位置上的逐点相等。范畴律全部
    从已有范畴继承。 *)

(** The preceding %\coqref{Cats.Cat.Shape.Ordinal.OrdinalShape}
    {%[OrdinalShape]%}% describes one ordered shape. %\coqref{Cats.Cat.Shape.Simplex.Core.SimplexCat}
    {%[SimplexCat]%}%
    describes how shapes of different dimensions are related. For example,
    selecting positions zero and two defines an arrow from dimension one to
    dimension two. The next chapter names such selections %\coqref{Cats.Cat.Shape.Simplex.Operators.Coface}
    {%[Coface]%}% and names
    adjacent identifications %\coqref{Cats.Cat.Shape.Simplex.Operators.Codegeneracy}
    {%[Codegeneracy]%}%.

    This category contains shapes and their operators, not yet a chosen
    collection of triangles or edges. A simplicial set will supply those
    values, reversing every operator's direction through
    %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict}
    {%[simplex_restrict]%}%. *)

(** 前一章的 %\coqref{Cats.Cat.Shape.Ordinal.OrdinalShape}
    {%[OrdinalShape]%}% 描述一个有序形状，%\coqref{Cats.Cat.Shape.Simplex.Core.SimplexCat}
    {%[SimplexCat]%}% 则描述不同维度
    的形状如何联系。例如，选取零与二这两个位置，就定义了从一维到二维的箭头。
    下一章把这种选取命名为 %\coqref{Cats.Cat.Shape.Simplex.Operators.Coface}
    {%[Coface]%}%，把相邻位置的合并命名为 %\coqref{Cats.Cat.Shape.Simplex.Operators.Codegeneracy}
    {%[Codegeneracy]%}%。

    这个范畴只包含形状及其算子，尚未指定一批三角形或边。单纯集合将提供这些
    值，并通过 %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict}
    {%[simplex_restrict]%}%
    反转每个算子的方向。 *)

Definition SimplexCat
  : Cat
  := @InducedCat CatCat nat OrdinalShape.

Notation Δ := SimplexCat.

(** The ordinal interpretation is the existing induced inclusion. *)

(** 序数解释直接使用已有的诱导嵌入。 *)

Definition SimplexInclusionF
  : Functor Δ CatCat
  := InducedInclusionF nat OrdinalShape.

(** The ordinal interpretation is fully faithful. *)

(** 序数解释为全忠实函子。 *)

Definition simplex_inclusion_fully_faithful
  : is_fully_faithful SimplexInclusionF
  := induced_inclusion_fully_faithful nat OrdinalShape.

(** Arrow equality can be checked by evaluating finite positions. *)

(** 箭头相等可以通过在有限位置处求值来检查。 *)

Definition simplex_eq_iff {n m : nat} (f g : (@Hom Δ) n m)
  : @HomEq Δ n m f g ↔ ∀ x, f x = g x
  := ordinal_functor_iso_iff f g.

(** Rank equations provide computational natural-isomorphism witnesses for
    simplex-arrow equations. *)

(** 编号方程为单纯箭头方程提供可计算的自然同构见证。 *)

Definition simplex_eq_of_rank {n m : nat} (f g : (@Hom Δ) n m)
    (H : ∀ x, fin_rank (f x) = fin_rank (g x))
  : @HomEq Δ n m f g
  := ordinal_functor_rank_iso f g H.
