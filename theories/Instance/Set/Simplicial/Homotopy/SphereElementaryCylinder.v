From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SpherePrismRelative.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * An Elementary Tetrahedron Gives a Relative Cylinder

    An elementary witness from x to y has faces [(b₂,b₂,x,y)]. Put
    [(s₀x,s₁x,w)] on the three staircase tetrahedra. The two common
    faces are x; all six external side faces are constant. The outer
    endpoint faces are y at time zero and x at time one, so the resulting
    directed cylinder runs from y to x. No time-reversal map of the
    simplicial interval is assumed.

    Reuse
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SpherePrismRelative.SpherePrismCylinder}
    {%[SpherePrismCylinder]%}% to glue these values with their complete
    relative boundary. Only the supplied tetrahedron and simplicial
    identities are needed, without Kan choices or coefficient classification.
    This is a single elementary step. Reversing or composing general
    cylinders and handling generated chains remain separate constructions. *)

(** * 一个初等四面体给出相对柱

    从 x 到 y 的初等见证具有面 [(b₂,b₂,x,y)]。将 [(s₀x,s₁x,w)] 放在三块
    阶梯四面体上；两个公共面均为 x，六个外侧面均为常值。外端点面在时间零
    为 y、时间一为 x，因此所得有向柱从 y 到 x。不预设单纯区间有时间反转映射。

    复用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SpherePrismRelative.SpherePrismCylinder}
    {%[SpherePrismCylinder]%}%，将这些值及其完整相对边界粘合。只需给定四面体
    和单纯恒等式，无需 Kan 选择或系数分类。这只是单个初等步骤；一般柱的反转、
    复合及生成链处理仍是独立构造。 *)

(** The arrows indicate restrictions to the shared faces. The lower
    arrow shows the time direction of the glued cylinder. *)

(** 箭头表示向公共面的限制；下方箭头标明粘合柱的时间方向。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
s_0x \arrow[r,"d_1"] & x & s_1x \arrow[l,"d_1"']
  \arrow[r,"d_2"] & x & w \arrow[l,"d_2"'] \\
y \arrow[rrrr,dashed,"{\mathrm{time}\ 0\to1}"'] &&&& x
\end{tikzcd}
\qquad $d_0w=d_1w=b_2,\quad d_3w=y.$
\end{center}%
*)

(** ** Three Supplied Pieces and Their Face Equations

    Fix independent simplex carrier/equality sizes, a base vertex and an
    actual elementary tetrahedron. All equations use specified equality;
    no equality of sphere-boundary or tetrahedron-law witnesses is used. *)

(** ** 三个给定块及其面方程

    固定独立的单形载体／相等大小、基点及实际初等四面体。全部方程使用指定
    相等，不使用球面边界或四面体定律见证的相等。 *)

Section ElementaryPrism.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context {x y : TwoSphereS X b} (H : TwoSphereHomotopy X b x y).

(** The third piece is the original tetrahedron, unchanged. *)

(** 第三块就是原四面体，保持不变。 *)

Definition two_sphere_homotopy_prism (i : Ordinal 2)
  : X 3
  := match fin_rank i with
  | 0 => s[X; 2; fin_first] x.1
  | 1 => s[X; 2; fin_first⁺] x.1
  | _ => H.1
  end.

(** Read all twelve faces. The four nontrivial degenerate side equations
    interchange a face and a degeneracy, then use the boundary of x. *)

(** 读取全部十二个面。四个非平凡退化侧面方程先交换面与退化，再使用 x 的边界。 *)

Lemma two_sphere_homotopy_prism_faces (i : Ordinal 2) (j : Ordinal 3)
  : d[X; 2; j] (two_sphere_homotopy_prism i) ≈S
      match fin_rank i, fin_rank j with
      | 0, 0 | 0, 1 | 1, 1 | 1, 2 | 2, 2 => x.1
      | 2, 3 => y.1
      | _, _ => simplex_constant X b 2
      end.
Proof.
  unfold two_sphere_homotopy_prism.
  destruct H as [w [H0 [H1 [H2 H3]]]].
  destruct i as [[] | [[] | [[] | []]]],
    j as [[] | [[] | [[] | [[] | []]]]];
    cbn [two_sphere_homotopy_prism fin_rank].
  - exact (simplex_face_degeneracy_id (X := X)
      (fin_first : Ordinal 2) x.1).
  - exact (simplex_face_degeneracy_next (X := X)
      (fin_first : Ordinal 2) x.1).
  - transitivity (s[X; 1; fin_first] (d[X; 1; fin_first⁺] x.1)).
    + exact (simplex_face_degeneracy_after (X := X)
        (fin_first⁺ : Ordinal 2) fin_first
        ltac:(cbn; repeat constructor) x.1).
    + transitivity (s[X; 1; fin_first] (simplex_constant X b 1)).
      * apply func_proper. exact (x.2 fin_first⁺).
      * apply simplex_constant_restrict.
  - transitivity (s[X; 1; fin_first] (d[X; 1; fin_first⁺⁺] x.1)).
    + exact (simplex_face_degeneracy_after (X := X)
        (fin_first⁺⁺ : Ordinal 2) fin_first
        ltac:(cbn; repeat constructor) x.1).
    + transitivity (s[X; 1; fin_first] (simplex_constant X b 1)).
      * apply func_proper. exact (x.2 fin_first⁺⁺).
      * apply simplex_constant_restrict.
  - transitivity (s[X; 1; fin_first] (d[X; 1; fin_first] x.1)).
    + exact (simplex_face_degeneracy_before (X := X)
        (fin_first : Ordinal 2) fin_first
        ltac:(cbn; repeat constructor) x.1).
    + transitivity (s[X; 1; fin_first] (simplex_constant X b 1)).
      * apply func_proper. exact (x.2 fin_first).
      * apply simplex_constant_restrict.
  - exact (simplex_face_degeneracy_id (X := X)
      (fin_first⁺ : Ordinal 2) x.1).
  - exact (simplex_face_degeneracy_next (X := X)
      (fin_first⁺ : Ordinal 2) x.1).
  - transitivity (s[X; 1; fin_first⁺] (d[X; 1; fin_first⁺⁺] x.1)).
    + exact (simplex_face_degeneracy_after (X := X)
        (fin_first⁺⁺ : Ordinal 2) fin_first⁺
        ltac:(cbn; repeat constructor) x.1).
    + transitivity (s[X; 1; fin_first⁺] (simplex_constant X b 1)).
      * apply func_proper. exact (x.2 fin_first⁺⁺).
      * apply simplex_constant_restrict.
  - exact H0.
  - exact H1.
  - exact H2.
  - exact H3.
Defined.

(** Both shared triangular faces are the same supplied sphere x. *)

(** 两个共享三角面均为同一个给定球面 x。 *)

Lemma two_sphere_homotopy_prism_adjacent (i : Ordinal 1)
  : d[X; 2; i↑⁺] (two_sphere_homotopy_prism i↑) ≈S
      d[X; 2; i↑⁺] (two_sphere_homotopy_prism i⁺).
Proof.
  destruct i as [[] | [[] | []]]; transitivity x.1.
  all: first [apply two_sphere_homotopy_prism_faces |
    symmetry; apply two_sphere_homotopy_prism_faces].
Defined.

(** The finite side criterion supplies the whole relative boundary after
    gluing, not only constant vertex trajectories. *)

(** 有限侧面判据在粘合后提供整个相对边界，而非仅有常值顶点轨迹。 *)

Definition two_sphere_homotopy_prism_relative
  : is_two_sphere_prism_relative X b two_sphere_homotopy_prism.
Proof.
  intros j k.
  destruct j as [[] | [[] | [[] | []]]], k as [[] | [[] | []]];
    apply two_sphere_homotopy_prism_faces.
Defined.

(** Reconstruct an actual cylinder in the order y to x. Neither reversing
    a general cylinder nor identifying its endpoints is needed. *)

(** 按 y 到 x 的顺序重构实际柱；不需要反转一般柱，也不识别两个端点。 *)

Definition TwoSphereHomotopyCylinder
  : TwoSphereCylinderHomotopy X b y x
  := SpherePrismCylinder X b two_sphere_homotopy_prism
      (two_sphere_homotopy_prism_adjacent fin_first)
      (two_sphere_homotopy_prism_adjacent fin_first⁺) y x
      (two_sphere_homotopy_prism_faces fin_first⁺⁺ fin_first⁺⁺⁺)
      (two_sphere_homotopy_prism_faces fin_first fin_first)
      two_sphere_homotopy_prism_relative.

(** Evaluation of the actual cylinder recovers every supplied piece,
    including the original elementary tetrahedron in position two. *)

(** 实际柱求值恢复每个给定块，包括位置二处原有的初等四面体。 *)

Lemma two_sphere_homotopy_cylinder_prism (i : Ordinal 2)
  : simplex_prism_eval (homotopy_map TwoSphereHomotopyCylinder.1) i ≈S
      two_sphere_homotopy_prism i.
Proof. apply simplex_triangle_prism_gluing_β. Defined.

End ElementaryPrism.

(** ** Specified Equality of Supplied Data

    Fix the same ambient object and vertex. Endpoints and tetrahedra may
    have different representatives and law witnesses. Only equality of
    the first sphere and the actual tetrahedra is needed to compare the
    prism values; the second endpoint is read from their last faces. *)

(** ** 给定数据的指定相等

    固定同一环境对象与顶点。端点及四面体可有不同代表和定律见证。比较棱柱值
    只需第一个球面及实际四面体相等；第二端点由其最后面读取。 *)

Section ElementaryPrismEquality.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context {x y x' y' : TwoSphereS X b}.
Context (H : TwoSphereHomotopy X b x y) (H' : TwoSphereHomotopy X b x' y').

(** Transport values through their underlying restrictions, without
    comparing sphere-boundary or elementary-homotopy proof fields. *)

(** 沿底层限制运输值，不比较球面边界或初等同伦的证明字段。 *)

Lemma two_sphere_homotopy_prism_proper (E : x ≈S x') (W : H.1 ≈S H'.1)
    (i : Ordinal 2)
  : two_sphere_homotopy_prism X b H i ≈S
      two_sphere_homotopy_prism X b H' i.
Proof.
  destruct i as [[] | [[] | [[] | []]]];
    cbn [two_sphere_homotopy_prism fin_rank].
  - apply func_proper. exact E.
  - apply func_proper. exact E.
  - exact W.
Defined.

(** The resulting actual maps are naturally equal even when their
    endpoint and relative-boundary witnesses are independently supplied. *)

(** 即使端点及相对边界见证独立给定，所得实际映射仍自然相等。 *)

Lemma two_sphere_homotopy_cylinder_map_proper (E : x ≈S x') (W : H.1 ≈S H'.1)
  : homotopy_map (TwoSphereHomotopyCylinder X b H).1 ≈N
      homotopy_map (TwoSphereHomotopyCylinder X b H').1.
Proof.
  apply simplex_triangle_prism_gluing_proper.
  exact (two_sphere_homotopy_prism_proper E W).
Defined.

End ElementaryPrismEquality.
