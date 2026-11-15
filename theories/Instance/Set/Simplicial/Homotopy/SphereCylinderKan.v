From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereTriangleInput
  Instance.Set.Simplicial.Homotopy.SphereTriangle
  Instance.Set.Simplicial.TriangleIteration.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Relative Composition and Reversal from Kan Choices

    The complete initial maps of
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereTriangleInput.SphereTriangleInputN}
    {%[SphereTriangleInputN]%}% now enter the actual nine-step
    %\coqref{Cats.Instance.Set.Simplicial.TriangleIteration.TriangleHornProductExtension}
    {%[TriangleHornProductExtension]%}%.
    Its restriction equation recovers the whole spatial boundary and both
    retained cylinder maps in every degree. Reading the remaining edge
    with the existing supplied-triangle theory gives actual relative
    composite and reverse cylinders.

    Only the nine stated three-/four-dimensional choices are supplied.
    Full Kan, uniqueness or respectfulness of the choosing functions are
    unnecessary. This does not prove independence of those choices or
    register an equivalence instance for directed cylinders. The optional
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderComparison.TwoSphereClassCylinder}
    {%[TwoSphereClassCylinder]%}% next uses these operations to interpret
    generated chains. General π₂ and weak equivalences remain separate. *)

(** * 从Kan选择构造实际相对复合与反向

    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereTriangleInput.SphereTriangleInputN}
    {%[SphereTriangleInputN]%}% 的完整初始映射，现输入实际九步
    %\coqref{Cats.Instance.Set.Simplicial.TriangleIteration.TriangleHornProductExtension}
    {%[TriangleHornProductExtension]%}%。其限制方程在每维恢复整个空间边界及
    两个保留柱映射，再由既有给定三角形理论读取剩余边，得到实际相对复合柱与反向柱。

    只给定所列九份三／四维选择，无需完整Kan、选择唯一或选择函数保相等。
    此处不证明选择独立，也不为有向柱自动注册等价实例；后续可选的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderComparison.TwoSphereClassCylinder}
    {%[TwoSphereClassCylinder]%}% 用这些操作解释生成链。一般π₂及弱等价的比较
    保持独立。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
A_0 \arrow[r,hook] \arrow[dr,"I"']
  & \Delta[2]\times\Delta[2] \arrow[d,dashed,"T"] \\
& X
\end{tikzcd}
\qquad
\begin{tikzcd}[column sep=large,row sep=large]
& y \arrow[dr,"K"] & \\
x \arrow[ur,"H"] \arrow[rr,dashed,"{\mathrm{composite}}"'] && z
\end{tikzcd}
\end{center}%
*)

(** ** Recovery for an Arbitrary Extension

    Fix independent carrier/equality sizes, X, its base vertex and the
    omitted time edge. First use an abstract extension and its restriction
    law; checking recovery never unfolds the computed nine-step map. *)

(** ** 任意延拓的恢复

    固定独立载体／相等界、X、基点及时间缺边。先使用抽象延拓及其限制律证明
    恢复；检查时不展开计算所得九步映射。 *)

Section RelativeExtensions.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (r : Ordinal 2).

(** The one restriction equation supplies full relative boundary and all
    retained-edge equations, without comparing any membership or law witnesses. *)

(** 一个限制方程即给出完整相对边界与全部保留边方程，不比较隶属或定律见证。 *)

Definition sphere_triangle_extension_recovery
    (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j))
    (E : cylinder_time_endpoint_matching r H)
    (T : TriangleHornAmbient ⇒ X)
    (F : (T ∘Nv RegionInclusionN (TriangleHornRegion r 0)) ≈N
      SphereTriangleInputN X b r H R E)
  : is_two_sphere_triangle_relative X b T *
      (∀ j, ¬ j = r → simplicial_triangle_edge T j ≈N H j).
Proof.
  split.
  - apply (snd (two_sphere_triangle_relative_iff X b T)). intros n a t.
    transitivity (SphereTriangleInputN X b r H R E n
      (triangle_input_generator r (inl (n; (a, t))))).
    + exact (F n (triangle_input_generator r (inl (n; (a, t))))).
    + exact (sphere_triangle_input_boundary_β X b r H R E n a t).
  - intros j Hj n [a t].
    transitivity (SphereTriangleInputN X b r H R E n
      (triangle_input_generator r (inr (j; (Hj, (n; (a, t))))))).
    + exact (F n (triangle_input_generator r
        (inr (j; (Hj, (n; (a, t))))))).
    + exact (sphere_triangle_input_face_β X b r H R E j Hj n (a, t)).
Defined.

(** The actual nine-step extension with full relative/retained-edge recovery.
    Each of its nine selection functions is explicit and independent. *)

(** 实际九步延拓及完整相对／保留边恢复；九个选择函数均显式且独立。 *)

Local Opaque TriangleHornProductExtension.

Definition SphereRelativeTriangleExtension
    (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s))
    (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j))
    (E : cylinder_time_endpoint_matching r H)
  : ∃ T : TriangleHornAmbient ⇒ X,
      (is_two_sphere_triangle_relative X b T *
        (∀ j, ¬ j = r → simplicial_triangle_edge T j ≈N H j))%type.
Proof.
  pose (e := TriangleHornProductExtension r K
    (SphereTriangleInputN X b r H R E)).
  exists e.1. exact (sphere_triangle_extension_recovery H R E e.1 e.2).
Defined.

Local Transparent TriangleHornProductExtension.

End RelativeExtensions.

(** ** Reading the Missing Cylinder

    Fix actual relative cylinders, retaining their original directions.
    The composite uses missing edge 02; the reverse uses missing edge 12.
    In both cases the output is exactly that edge of the selected triangle. *)

(** ** 读取缺失柱

    固定实际相对柱，保留其原方向。复合读取缺02边，反向读取缺12边；两种输出
    都恰为所选三角形的相应边。 *)

Section CylinderOperations.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context {x y z : TwoSphereS X b}.

Local Opaque SphereRelativeTriangleExtension.

(** Compose H from x to y with L from y to z, using nine choices for the
    missing long edge. No already supplied triangle is required. *)

(** 用缺长边对应的九份选择，将x到y的H与y到z的L复合；不要求预先给定三角形。 *)

Definition SphereCylinderComposite
    (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first⁺ s))
    (H : TwoSphereCylinderHomotopy X b x y)
    (L : TwoSphereCylinderHomotopy X b y z)
  : TwoSphereCylinderHomotopy X b x z.
Proof.
  pose (e := SphereRelativeTriangleExtension X b fin_first⁺ K
    (SphereCompositeEdges X b H L) (sphere_composite_edges_relative X b H L)
    (sphere_composite_edges_endpoints X b H L)).
  exact (SphereTriangleComposite X b e.1 (fst e.2) H L
    (snd e.2 fin_first⁺⁺ (ltac:(discriminate)))
    (snd e.2 fin_first (ltac:(discriminate)))).
Defined.

(** Reverse H from x to y using nine choices for the missing edge 12.
    This is a constructed relative cylinder from y to x. *)

(** 用缺12边对应的九份选择，反转x到y的H，构造实际的y到x相对柱。 *)

Definition SphereCylinderReverse
    (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
    (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b y x.
Proof.
  pose (e := SphereRelativeTriangleExtension X b fin_first K
    (SphereReverseEdges X b H) (sphere_reverse_edges_relative X b H)
    (sphere_reverse_edges_endpoints X b H)).
  exact (SphereTriangleReverse X b e.1 (fst e.2) H
    (snd e.2 fin_first⁺⁺ (ltac:(discriminate)))
    (snd e.2 fin_first⁺ (ltac:(discriminate)))).
Defined.

(** The actual composite map is the selected triangle's long edge. *)

(** 实际复合映射是所选三角形的长边。 *)

Definition sphere_cylinder_composite_map
    (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first⁺ s))
    (H : TwoSphereCylinderHomotopy X b x y)
    (L : TwoSphereCylinderHomotopy X b y z)
  : homotopy_map (SphereCylinderComposite K H L).1 ≈N
      simplicial_triangle_edge
        (SphereRelativeTriangleExtension X b fin_first⁺ K
          (SphereCompositeEdges X b H L)
          (sphere_composite_edges_relative X b H L)
          (sphere_composite_edges_endpoints X b H L)).1 fin_first⁺.
Proof. reflexivity. Defined.

(** The actual reverse map is the selected triangle's edge 12. *)

(** 实际反向映射是所选三角形的12边。 *)

Definition sphere_cylinder_reverse_map
    (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
    (H : TwoSphereCylinderHomotopy X b x y)
  : homotopy_map (SphereCylinderReverse K H).1 ≈N
      simplicial_triangle_edge
        (SphereRelativeTriangleExtension X b fin_first K
          (SphereReverseEdges X b H)
          (sphere_reverse_edges_relative X b H)
          (sphere_reverse_edges_endpoints X b H)).1 fin_first.
Proof. reflexivity. Defined.

Local Transparent SphereRelativeTriangleExtension.

End CylinderOperations.
