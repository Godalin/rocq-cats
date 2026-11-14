From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Set.Simplicial.Homotopy.SphereFaceHomotopy
  Instance.Set.Simplicial.Homotopy.SphereUnit.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Relative Cylinders Give Generated Sphere-Class Equality

    A full relative cylinder has three actual staircase tetrahedra.
    Their face table was proved in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two_sphere_prism_faces}
    {%[two_sphere_prism_faces]%}%. First give the two internal triangles
    their based boundary witnesses, using the whole relative boundary at
    their restricted time operators. Keeping endpoints fixed alone would
    not supply those equations.

    Read the first tetrahedron as a low-face homotopy from y to D011,
    the middle as a composite of b₂ with D011 into D001, and the last
    as a standard elementary homotopy from D001 to x. The integrated
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFaceHomotopy.SphereLowHomotopy}
    {%[SphereLowHomotopy]%}% converts the first. For the middle, compare
    with the existing left-unit tetrahedron, without selecting a product.
    These three steps give generated class equality between x and y.

    Only four-dimensional missing-face-one and missing-face-two choices
    are used. No three-dimensional filling, selected multiplication or
    Group, coefficient classification, cancellation or full Kan is
    required. All original cylinder and prism data are retained. This
    proves one direction of the general comparison; the reverse, general
    Kan commutativity/π₂ identification and arbitrary-path base change
    remain further work. *)

(** * 相对柱给出生成球面类相等

    完整相对柱具有三个实际阶梯四面体；其面表已经由
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two_sphere_prism_faces}
    {%[two_sphere_prism_faces]%}% 证明。先在限制后的时间算子处使用整个相对
    边界，为两个内部三角形给出基点边界见证。仅固定端点不能提供这些方程。

    将第一块四面体读成从 y 到 D011 的低索引面同伦；中间一块读成常值 b₂
    与 D011 合成到 D001 的见证；最后一块读成从 D001 到 x 的标准初等同伦。
    已集成的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFaceHomotopy.SphereLowHomotopy}
    {%[SphereLowHomotopy]%}% 转换第一块。对中间一块，只需与既有左单位四面体
    比较，无须选择乘法。三个步骤给出 x 与 y 之间的生成类相等。

    只使用四维缺第一面及缺第二面选择，不要求三维填充、选定乘法或群、系数
    分类、消去律或完整 Kan。原有柱及棱柱数据全部保留。这只证明一般比较的
    一个方向；反向、一般 Kan 交换性／π₂ 识别及任意路径换基仍需后续工作。 *)

(** The arrows denote generated class equalities, with actual tetrahedron
    witnesses at the first and last step and output comparison in between.
    The final theorem reverses this displayed chain. *)

(** 箭头表示生成类相等；首尾步骤带有实际四面体见证，中间步骤使用输出比较。
    最终定理将所显示的链反向。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large]
[y] \arrow[r,"{w_0}"] & [D_{011}]
  \arrow[r,"{w_1,\ s_1D_{011}}"] & [D_{001}]
  \arrow[r,"{w_2}"] & [x]
\end{tikzcd}
\end{center}%
*)

(** ** The Actual Diagonals and Three Prism Witnesses

    Fix independent carrier/equality sizes, a base vertex and a complete
    relative cylinder. No horn selections enter these constructions. *)

(** ** 实际对角面与三个棱柱见证

    固定独立载体／相等大小、基点及完整相对柱。这些构造不带 horn 选择。 *)

Section CylinderPrismWitnesses.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context {x y : TwoSphereS X b} (H : TwoSphereCylinderHomotopy X b x y).

(** Restrict the time coordinate as well as the spatial coface before
    applying the full relative boundary law. *)

(** 先同时限制时间坐标及空间余面，再应用完整相对边界定律。 *)

Lemma two_sphere_cylinder_diagonal_boundary (i : Ordinal 1) (j : Ordinal 2)
  : d[X; 1; j] (two_sphere_cylinder_diagonal H i) ≈S
      simplex_constant X b 1.
Proof.
  transitivity (two_sphere_cylinder_eval X b H
    (id ∘ δ[1; j]) (σ[1; i] ∘ δ[1; j])).
  - exact (two_sphere_cylinder_restrict X b H δ[1; j] id σ[1; i]).
  - transitivity (two_sphere_cylinder_eval X b H
      δ[1; j] (σ[1; i] ∘ δ[1; j])).
    + apply two_sphere_cylinder_eval_proper; [apply comp_id_l | reflexivity].
    + exact (two_sphere_cylinder_boundary X b H
        δ[1; j] (σ[1; i] ∘ δ[1; j]) (boundary_face_member j)).
Defined.

(** Keep the original diagonal triangle; add only its boundary witnesses. *)

(** 保留原对角三角形，仅增加其边界见证。 *)

Definition TwoSphereCylinderDiagonal (i : Ordinal 1)
  : TwoSphereS X b
  := (two_sphere_cylinder_diagonal H i;
      two_sphere_cylinder_diagonal_boundary i).

(** The first actual prism has y and D011 in its first two faces. *)

(** 第一块实际棱柱的最前两面为 y 与 D011。 *)

Definition SphereCylinderFirstLowHomotopy
  : TwoSphereLowHomotopy X b y (TwoSphereCylinderDiagonal fin_first⁺).
Proof.
  exists (two_sphere_prism H fin_first). split; [| split; [| split]].
  - exact (two_sphere_prism_faces H fin_first fin_first).
  - exact (two_sphere_prism_faces H fin_first fin_first⁺).
  - exact (two_sphere_prism_faces H fin_first fin_first⁺⁺).
  - exact (two_sphere_prism_faces H fin_first fin_first⁺⁺⁺).
Defined.

(** The middle prism is a supplied composite, not a selected product. *)

(** 中间棱柱是给定合成，而非选定乘积。 *)

Definition SphereCylinderMiddleComposite
  : TwoSphereComposite X b (two_sphere_base X b)
      (TwoSphereCylinderDiagonal fin_first⁺)
      (TwoSphereCylinderDiagonal fin_first).
Proof.
  exists (two_sphere_prism H fin_first⁺). split; [| split; [| split]].
  - exact (two_sphere_prism_faces H fin_first⁺ fin_first).
  - exact (two_sphere_prism_faces H fin_first⁺ fin_first⁺).
  - exact (two_sphere_prism_faces H fin_first⁺ fin_first⁺⁺).
  - exact (two_sphere_prism_faces H fin_first⁺ fin_first⁺⁺⁺).
Defined.

(** The final prism is already a standard elementary homotopy. *)

(** 最后一块棱柱已经是标准初等同伦。 *)

Definition SphereCylinderLastHomotopy
  : TwoSphereHomotopy X b (TwoSphereCylinderDiagonal fin_first) x.
Proof.
  exists (two_sphere_prism H fin_first⁺⁺). split; [| split; [| split]].
  - exact (two_sphere_prism_faces H fin_first⁺⁺ fin_first).
  - exact (two_sphere_prism_faces H fin_first⁺⁺ fin_first⁺).
  - exact (two_sphere_prism_faces H fin_first⁺⁺ fin_first⁺⁺).
  - exact (two_sphere_prism_faces H fin_first⁺⁺ fin_first⁺⁺⁺).
Defined.

End CylinderPrismWitnesses.

(** ** Descending a Full Relative Cylinder

    Fix only the two four-dimensional comparison choices. Reuse actual
    unit composites and generated class symmetry/transitivity; do not
    register an equivalence structure for the directed cylinder relation. *)

(** ** 下降完整相对柱

    只固定两项四维比较选择。复用实际单位合成及生成类对称／传递性，不为有向
    柱关系注册等价结构。 *)

Section CylinderClassDescent.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX1 : !HasHornFillers X 4 fin_first⁺}.
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.

(** Every actual full relative cylinder gives generated sphere-class
    equality, without reflecting that equality to native triangles. *)

(** 每份实际完整相对柱都给出生成球面类相等，不将该相等反映为原生三角形相等。 *)

Lemma two_sphere_cylinder_class {x y : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy X b x y)
  : (x : TwoSphereClassS X b) ≈S y.
Proof.
  symmetry.
  transitivity (TwoSphereCylinderDiagonal X b H fin_first⁺
    : TwoSphereClassS X b).
  - exact (two_sphere_low_homotopy_class X b
      (SphereCylinderFirstLowHomotopy X b H)).
  - transitivity (TwoSphereCylinderDiagonal X b H fin_first
      : TwoSphereClassS X b).
    + exact (two_sphere_composite_output_eq X b
        (SphereLeftUnitComposite X b
          (TwoSphereCylinderDiagonal X b H fin_first⁺))
        (SphereCylinderMiddleComposite X b H)).
    + exact (two_sphere_class_step X b (SphereCylinderLastHomotopy X b H)).
Defined.

End CylinderClassDescent.
