From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Low
  Instance.Bool.Group.

Local Existing Instance BoolS_Monoid.

(** * A Boolean Cocycle Simplicial Set

    The construction %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Core.TwoCocycleSimplicial}
    {%[TwoCocycleSimplicial]%}% is now an actual simplicial set with Boolean
    coefficients. It has one vertex and one edge in specified equality,
    but its two-dimensional data retain a Boolean coefficient.

    There are two distinct triangles with exactly the same three edges.
    The unit triangle is degenerate; the triangle labelled [true] is not
    equal to any degeneracy of an edge. These are statements about this
    simplicial set and its specified equality. They do not compute a
    homotopy group or establish Kan filling. In particular the earlier
    %\coqref{Cats.Instance.Bool.Cocycle.BoolTriangleCocycle}
    {%[BoolTriangleCocycle]%}% being a nonzero coboundary is not an argument
    for a nonzero homotopy group. *)

(** * 布尔 cocycle 单纯集合

    现在将 %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Core.TwoCocycleSimplicial}
    {%[TwoCocycleSimplicial]%}% 实例化为布尔系数的实际单纯集合。按指定相等，
    它只有一个顶点和一条边，二维数据却保留一个布尔系数。

    两个不同的三角形具有相同的三条边。单位三角形为退化单形；标签为 [true]
    的三角形不与任何由边退化而来的单形相等。这些结论针对该单纯集合及其
    指定相等，并未计算同伦群或证明 Kan 填充。特别地，前面的
    %\coqref{Cats.Instance.Bool.Cocycle.BoolTriangleCocycle}
    {%[BoolTriangleCocycle]%}% 是非零余边界，并不能作为同伦群非零的论证。 *)

(** Choose the existing xor monoid explicitly, in the smallest ambient sizes.
    Importing the module does not globally register that chosen monoid. *)

(** 显式选择已有异或幺半群，采用最小环境大小；导入模块不会全局注册该选定
    幺半群。 *)

Definition BoolCocycleModel
  : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Z²(BoolS).

(** A two-simplex whose increasing triangle has coefficient [true]. *)

(** 严格递增三角形系数为 [true] 的二维单形。 *)

Definition bool_cocycle_triangle
  : BoolCocycleModel 2
  := two_cocycle_triangle_resp true.

(** The distinguished unit-labelled two-simplex. *)

(** 指定的单位标签二维单形。 *)

Definition bool_cocycle_unit_triangle
  : BoolCocycleModel 2
  := two_cocycle_simplex_unit 2.

(** The actual label computes, rather than being recovered by choice. *)

(** 实际标签可以直接计算，而非依靠选择来恢复。 *)

Lemma bool_cocycle_triangle_value
  : two_cocycle_triangle_value_resp bool_cocycle_triangle = true.
Proof. reflexivity. Defined.

(** The two triangles remain distinct in the model's specified equality. *)

(** 两个三角形在模型的指定相等下仍然不同。 *)

Lemma bool_cocycle_triangle_not_unit
  : ¬ (bool_cocycle_triangle ≈S bool_cocycle_unit_triangle).
Proof.
  intros [H].
  pose proof (H fin_first (fin_next fin_first)
    (fin_next (fin_next fin_first))
    (ordinal_step (@fin_first 1))
    (ordinal_step (fin_next (@fin_first 0)))) as E.
  change (true = false) in E. discriminate E.
Defined.

(** Each of their three corresponding faces is equal to the same edge. *)

(** 两个三角形的三个对应面均等于同一条边。 *)

Lemma bool_cocycle_same_edges (i : Fin@{Set} 3)
  : d[BoolCocycleModel; 1; i] bool_cocycle_triangle ≈S
      d[BoolCocycleModel; 1; i] bool_cocycle_unit_triangle.
Proof. apply two_cocycle_one_unique. Defined.

(** Degenerating any edge at either position cannot produce this triangle. *)

(** 在任一位置退化任意边，都不能产生这个三角形。 *)

Lemma bool_cocycle_triangle_not_degenerate
    (e : BoolCocycleModel 1) (i : Fin@{Set} 2)
  : ¬ (bool_cocycle_triangle ≈S s[BoolCocycleModel; 1; i] e).
Proof.
  intro H. apply bool_cocycle_triangle_not_unit.
  transitivity (s[BoolCocycleModel; 1; i] e);
    [exact H | apply two_cocycle_degenerate_one].
Defined.
