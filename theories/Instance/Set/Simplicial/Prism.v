From Cats Require Export
  Instance.Set.Simplicial.Homotopy.Core
  Cat.Shape.Simplex.Prism.
From Cats Require Import
  Cat.Core
  Cat.Natural.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Reading Cylinder Maps from Their Staircase Simplices

    The shape factorization
    %\coqref{Cats.Cat.Shape.Simplex.Prism.SimplexPrismFactor}
    {%[SimplexPrismFactor]%}% covers every degree of a standard simplex
    cylinder, including degenerate simplices. Naturality therefore reads
    any given cylinder map from its m+1 maximal staircase values. This
    proves determination, not existence of a map from arbitrary values.
    The later
    %\coqref{Cats.Instance.Set.Simplicial.PrismGluing.SimplexPrismGluingN}
    {%[SimplexPrismGluingN]%}% constructs that map when all spatial/time
    overlaps are compatible. The sphere
    cylinder client
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two_sphere_cylinder_factor}
    {%[two_sphere_cylinder_factor]%}% applies this to the original three
    prism tetrahedra without changing their stored data. *)

(** * 从阶梯单形读取柱映射

    形状分解 %\coqref{Cats.Cat.Shape.Simplex.Prism.SimplexPrismFactor}
    {%[SimplexPrismFactor]%}% 覆盖标准单形柱的每一维，包括退化单形。
    因此，自然性可从 m+1 个最大阶梯值读取任意给定柱映射。这只证明确定性，
    不从任意给定值构造映射。后续的
    %\coqref{Cats.Instance.Set.Simplicial.PrismGluing.SimplexPrismGluingN}
    {%[SimplexPrismGluingN]%}% 在全部空间／时间交叠相容时构造该映射。球面柱客户端
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two_sphere_cylinder_factor}
    {%[two_sphere_cylinder_factor]%}% 将其应用于原有三个棱柱四面体，
    保留其原有数据。 *)

(** ** Evaluating a Given Cylinder Map

    Fix independent simplex carrier/equality bounds, any target X and a
    spatial dimension m. No Kan structure or chosen value equality is
    needed; all comparisons are in the target's specified equality. *)

(** ** 求值给定柱映射

    固定独立单形载体／相等界、任意目标 X 及空间维数 m。不要求 Kan 结构或
    额外选定相等；所有比较均在目标的指定相等中进行。 *)

Section PrismMaps.
Universes u p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {m : nat}.

Let D
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[m].

(** Read a map at one maximal staircase, retaining its actual value. *)

(** 在一块最大阶梯处读取映射，保留实际值。 *)

Definition simplex_prism_eval (K : SimplicialCylinderF D ⇒ X)
    (k : Ordinal m)
  : X (S m)
  := K (S m) ({|lower := σ[m; k]|}, {|lower := SimplexPrismTimeF k|}).

(** Any simplex value is the restriction of the computed staircase value.
    The pivot may change under restriction; the actual factor remains
    the interleaved spatial/time operator. *)

(** 任意单形值均为计算所得阶梯值的限制。限制可以改变枢轴，而实际因子始终
    是空间／时间交织算子。 *)

Lemma simplex_prism_eval_factor (K : SimplicialCylinderF D ⇒ X)
    {n : nat} (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : K n ({|lower := a|}, {|lower := t|}) ≈S
      X[SimplexPrismIndexF a t]Δ (simplex_prism_eval K
        (simplex_prism_pivot a t)).
Proof.
  pose (P := SimplexPrismFactor a t).
  transitivity (K n
    ({|lower := σ[m; P.1] ∘ P.2.1|},
     {|lower := SimplexPrismTimeF P.1 ∘ P.2.1|})).
  - apply func_proper. split;
      refine {|lower := _|}; symmetry; [exact (fst P.2.2) | exact (snd P.2.2)].
  - exact (simplex_restrict_natural K P.2.1
      ({|lower := σ[m; P.1]|}, {|lower := SimplexPrismTimeF P.1|})).
Defined.

(** Two given maps agree in every degree exactly when they agree on all
    maximal staircases. Equality of function or naturality proof records
    is unnecessary; this is not a filler uniqueness statement. *)

(** 两个给定映射逐维相等，当且仅当它们在全部最大阶梯上相等。不需要函数或
    自然性证明记录相等；此处也不是填充唯一性结论。 *)

Lemma simplex_prism_map_eq_iff (K L : SimplicialCylinderF D ⇒ X)
  : (K ≈N L) ↔ ∀ k, simplex_prism_eval K k ≈S simplex_prism_eval L k.
Proof.
  split.
  - intros E k. exact (E (S m)
      ({|lower := σ[m; k]|}, {|lower := SimplexPrismTimeF k|})).
  - intros E n [[a] [t]].
    transitivity (X[SimplexPrismIndexF a t]Δ
      (simplex_prism_eval K (simplex_prism_pivot a t))).
    + apply simplex_prism_eval_factor.
    + transitivity (X[SimplexPrismIndexF a t]Δ
        (simplex_prism_eval L (simplex_prism_pivot a t))).
      * apply func_proper. apply E.
      * symmetry. apply simplex_prism_eval_factor.
Defined.

End PrismMaps.
