From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Homotopy.
From Cats Require
  Instance.Set.Simplicial.Vertex.Sphere.
From Cats Require Import
  Cat.Core
  Cat.Natural.

Import Cats.Instance.Set.Groupoid (EqGpd).
Import Cats.Instance.Set.Simplicial.Vertex.Core (VertexNerve).
Import Cats.Instance.Set.Simplicial.Vertex.Sphere (vertex_two_sphere_unique).

Local Open Scope nat_scope.
Local Open Scope monoid_scope.

(** * An Ordinary Nerve Cannot Recover Nontrivial Sphere Coefficients

    Suppose maps go from the cocycle model into an ordinary category nerve
    and back. The first map sends every based sphere to the same sphere,
    by %\coqref{Cats.Instance.Set.Simplicial.Vertex.Sphere.vertex two sphere unique}
    {%[vertex_two_sphere_unique]%}%. The round trip therefore gives the
    same triangle for every source sphere, in specified equality.

    If this round trip were linked to the identity by finitely many actual
    cylinder homotopies, reversals and natural equalities, the descended
    coefficient invariant would identify every coefficient with the unit.
    A nonunit coefficient rules out that retraction. This concerns actual
    maps and the stated generated homotopy relation; it does not identify
    weak equivalences or classify all 1-types. No groupoid hypothesis on
    the ordinary category is needed. *)

(** * 普通 Nerve 无法恢复非平凡球面系数

    假设存在从 cocycle 模型到普通范畴 nerve 再返回的映射。由
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Sphere.vertex two sphere unique}
    {%[vertex_two_sphere_unique]%}%，第一个映射将每个基点球面送到同一个
    球面。因此，往返对全部源球面给出按指定相等相同的三角形。

    若此往返能经有限次实际柱同伦、反向及自然相等联系到恒等映射，则下降后的
    系数不变量会将每个系数识别为单位。非单位系数排除这种收缩。此结论针对
    实际映射及所述生成同伦关系，不识别弱等价，也不分类所有 1-types。
    对普通范畴不要求群胚假设。 *)

(** For any proposed pair of maps, the upper path collapses all sphere
    coefficients to the same value. The lower path is the identity and
    retains each coefficient. A homotopy chain between these parallel
    maps would make their evaluations agree, forcing a to equal the unit. *)

(** 对任意候选映射对，上方路径将全部球面系数送到同一个值，下方恒等路径则
    保留每个系数。若平行路径之间存在同伦链，两者求值必相等，迫使 a 等于
    单位。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
Z^2(M) \arrow[r,"{f}"] \arrow[rr,bend right=30,"{\operatorname{id}}"'] &
N(T) \arrow[r,"{g}"] & Z^2(M)
\end{tikzcd}
\end{center}
\begin{center}
\begin{tikzcd}[column sep=large]
a \arrow[r,mapsto,"{g f}"] & c(gf(x_a))
  \arrow[r,equal] & c(gf(x_1)) & 1 \arrow[l,mapsto,"{g f}"']
\end{tikzcd}
\end{center}%
*)

(** ** A Round Trip through an Arbitrary Category Nerve

    Fix a coefficient monoid, an object presentation of any category,
    common ambient bounds and the two actual simplicial maps. Native
    category hom and equality sizes remain independent. *)

(** ** 经任意范畴 Nerve 的往返

    固定系数幺半群、任意范畴的对象呈现、共同环境界及两个实际单纯映射。
    范畴原生 Hom 与相等大小保持独立。 *)

Section NerveRetraction.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}
    {A : SetC} {C : Cat} (T : Functor (EqGpd A) C).

Let Z
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

Let N
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := VertexNerve T.

Context (f : Z ⇒ N) (g : N ⇒ Z).

(** The round trip sends any two source spheres to equal triangles,
    using only nerve sphere uniqueness and respectfulness of the return. *)

(** 只用 nerve 球面唯一性及返回映射的保相等性，往返便将任意两个源球面送到
    相等三角形。 *)

Lemma cocycle_nerve_roundtrip_sphere
    (x y : TwoSphereS Z (two_cocycle_simplex_unit 0))
  : g 2 (f 2 x.1) ≈S g 2 (f 2 y.1).
Proof.
  apply func_proper.
  exact (vertex_two_sphere_unique T (f 0 (two_cocycle_simplex_unit 0))
    (two_sphere_map_resp f (two_cocycle_simplex_unit 0) x)
    (two_sphere_map_resp f (two_cocycle_simplex_unit 0) y)).
Defined.

(** A generated cylinder-homotopy retraction would force every
    coefficient to be the unit. Evaluate the same map-chain on the free
    sphere and the constant sphere; no transport of inverse witnesses
    or general homotopy-group invariance is assumed. *)

(** 生成柱同伦意义下的收缩会迫使每个系数为单位。将同一映射链分别作用于
    自由球面和常值球面；不预设逆见证运输或一般同伦群不变性。 *)

Lemma cocycle_nerve_homotopy_retract_trivial
    (H : (g ∘Nv f : @CocycleHomotopyMapS M HM Z) ≈S idN) (a : M)
  : a ≈S 1.
Proof.
  pose (b := (two_cocycle_simplex_unit 0 : Z 0)).
  pose (x := (cocycle_two_sphere_resp a : TwoSphereS Z b)).
  pose (y := two_sphere_base Z b).
  pose proof (@func_proper _ _
    (@cocycle_homotopy_evaluation_resp M HM Z b x) _ _ H) as Ex.
  pose proof (@func_proper _ _
    (@cocycle_homotopy_evaluation_resp M HM Z b y) _ _ H) as Ey.
  change (two_cocycle_triangle_value_resp (g 2 (f 2 x.1)) ≈S
    two_cocycle_triangle_value_resp x.1) in Ex.
  change (two_cocycle_triangle_value_resp (g 2 (f 2 y.1)) ≈S
    two_cocycle_triangle_value_resp y.1) in Ey.
  transitivity (two_cocycle_triangle_value_resp x.1).
  - symmetry. apply two_cocycle_triangle_β.
  - transitivity (two_cocycle_triangle_value_resp (g 2 (f 2 x.1))).
    + symmetry. exact Ex.
    + transitivity (two_cocycle_triangle_value_resp (g 2 (f 2 y.1))).
      * apply func_proper. apply cocycle_nerve_roundtrip_sphere.
      * transitivity (two_cocycle_triangle_value_resp y.1).
        -- exact Ey.
        -- apply cocycle_constant_triangle_value.
Defined.

(** A witnessed nonunit coefficient excludes every such round trip. *)

(** 一份系数非单位的见证排除每个这样的往返。 *)

Definition cocycle_no_nerve_homotopy_retract (a : M) (Ha : ¬ a ≈S 1)
  : ¬ (g ∘Nv f : @CocycleHomotopyMapS M HM Z) ≈S idN.
Proof.
  intros H. exact (Ha (cocycle_nerve_homotopy_retract_trivial H a)).
Defined.

End NerveRetraction.
