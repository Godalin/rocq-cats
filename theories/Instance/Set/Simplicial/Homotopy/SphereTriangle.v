From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Set.Simplicial.Homotopy.Triangle.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Relative Triangle Extensions of Sphere Cylinders

    A supplied map [Δ[2] × Δ[2] ⇒ X] uses the first factor for space and
    the second for the parameter triangle. Require its whole spatial
    boundary to be constant, for arbitrary parameter simplices. Then the
    generic edge restrictions give actual relative composite or reverse
    cylinders whenever the required two edge equations are supplied.

    Here the triangle remains supplied. The subsequent
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderKan.SphereCylinderComposite}
    {%[SphereCylinderComposite]%}% and
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderKan.SphereCylinderReverse}
    {%[SphereCylinderReverse]%}% construct actual output cylinders using
    nine explicit choices, reusing the restrictions in this module.
    The earlier
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder.TwoSphereHomotopyCylinder}
    {%[TwoSphereHomotopyCylinder]%}% has direction y to x; its direction
    cannot be silently reversed without supplying
    further data. Generated chains, general π₂ and weak-equivalence
    comparison remain separate work. The new construction combines the
    actual nine-step geometry with the complete relative initial maps. *)

(** * 球面柱的相对三角延拓

    给定映射 [Δ[2] × Δ[2] ⇒ X]，第一因子为空间，第二因子为参数三角形。
    要求整个空间边界对任意参数单形均为常值；再给所需两个边方程，通用边限制
    就给出实际相对复合柱或反向柱。

    此处仍给定三角形。后续的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderKan.SphereCylinderComposite}
    {%[SphereCylinderComposite]%}% 与
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderKan.SphereCylinderReverse}
    {%[SphereCylinderReverse]%}% 用九份显式选择构造实际输出柱，复用本章的限制。
    先前的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder.TwoSphereHomotopyCylinder}
    {%[TwoSphereHomotopyCylinder]%}% 方向为 y 到 x，不能在没有额外数据时
    悄然反转；生成链、一般 π₂ 及弱等价比较仍是独立工作。
    新构造将实际九步几何与完整相对初始映射组合起来。 *)

(** ** Fixing All Spatial Boundary Simplices

    Fix independent carrier/equality sizes, X and a base vertex. Express
    the boundary prescription through the actual boundary inclusion and
    constant-sphere map, so its transport is already natural. *)

(** ** 固定全部空间边界单形

    固定独立载体／相等大小、X 及基点。通过实际边界包含和常球面映射表达边界
    给定值，使其运输已为自然映射。 *)

Section SphereTriangles.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

Let D
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[2].

(** Every parameter triangle simplex keeps the entire spatial boundary
    at the constant sphere, not only its vertices or parameter endpoints. *)

(** 每个参数三角单形都将整个空间边界固定于常球面，而非仅固定其顶点或参数端点。 *)

Definition is_two_sphere_triangle_relative (T : SimplicialParameterF D 2 ⇒ X)
  : Type
  := is_simplicial_parameter_relative ι∂[2]
      (⟦(two_sphere_base X b).1⟧Δ[X; 2] ∘Nv ι∂[2]) T.

(** The coherent prescription is exactly the all-degree constant law. *)

(** 相干给定值恰好等同于每维的常值定律。 *)

Definition two_sphere_triangle_relative_iff (T : SimplicialParameterF D 2 ⇒ X)
  : is_two_sphere_triangle_relative T ↔
      ∀ n (a : (∂Δ[2]) n) (t : (Δ[2]) n),
        T n (ι∂[2] n a, t) ≈S simplex_constant X b n.
Proof.
  split; intros R n a t.
  - transitivity ((⟦(two_sphere_base X b).1⟧Δ[X; 2] ∘Nv ι∂[2]) n a).
    + exact (R n a t).
    + exact (simplex_constant_restrict X b (lower a).1).
  - transitivity (simplex_constant X b n).
    + exact (R n a t).
    + symmetry. exact (simplex_constant_restrict X b (lower a).1).
Defined.

(** Read a relative composite from a supplied extension of two cylinders.
    The output map is precisely edge 02 of that extension. *)

(** 从给定的两个柱的延拓读取相对复合；输出映射恰为延拓的边 02。 *)

Definition SphereTriangleComposite
    (T : SimplicialParameterF D 2 ⇒ X) (R : is_two_sphere_triangle_relative T)
    {x y z : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy X b x y)
    (K : TwoSphereCylinderHomotopy X b y z)
    (E01 : simplicial_triangle_edge T fin_first⁺⁺ ≈N homotopy_map H.1)
    (E12 : simplicial_triangle_edge T fin_first ≈N homotopy_map K.1)
  : TwoSphereCylinderHomotopy X b x z.
Proof.
  exists (SimplicialTriangleComposite T H.1 K.1 E01 E12).
  intros n a t. exact (fst (two_sphere_triangle_relative_iff T) R n a
    (fmap StandardSimplexF δ[1; fin_first⁺] n t)).
Defined.

(** Read a relative reverse when edge 01 is the supplied cylinder and
    edge 02 is constant at its initial sphere. Existence of T is explicit. *)

(** 当边 01 为给定柱、边 02 为其初始球面处的常柱时读取相对反向；T 的存在显式给定。 *)

Definition SphereTriangleReverse
    (T : SimplicialParameterF D 2 ⇒ X) (R : is_two_sphere_triangle_relative T)
    {x y : TwoSphereS X b} (H : TwoSphereCylinderHomotopy X b x y)
    (E01 : simplicial_triangle_edge T fin_first⁺⁺ ≈N homotopy_map H.1)
    (E02 : simplicial_triangle_edge T fin_first⁺ ≈N
      homotopy_map (SimplicialConstantHomotopy ⟦x.1⟧Δ[X; 2]))
  : TwoSphereCylinderHomotopy X b y x.
Proof.
  exists (SimplicialTriangleReverse T H.1 E01 E02).
  intros n a t. exact (fst (two_sphere_triangle_relative_iff T) R n a
    (fmap StandardSimplexF δ[1; fin_first] n t)).
Defined.

End SphereTriangles.
