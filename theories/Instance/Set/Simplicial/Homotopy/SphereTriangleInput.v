From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Set.Simplicial.Homotopy.TimeOverlap
  Instance.Set.Simplicial.TriangleInput.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Relative Data for the Initial Triangle Region

    The initial region contains the whole spatial boundary and two time
    edges. Its boundary prescription is constant at the base vertex.
    Relative cylinder laws give boundary-edge agreement, while actual
    homotopy endpoint equations give the common-time compatibility via
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.TimeOverlap.cylinder_time_factors_from_endpoints}
    {%[cylinder_time_factors_from_endpoints]%}%.
    The initial map itself is the already constructed
    %\coqref{Cats.Instance.Set.Simplicial.TriangleInput.TriangleInputN}
    {%[TriangleInputN]%}%; no new descent proof is needed.

    For composition retain edges 01 and 12 (missing edge 02). For reversal
    retain edge 01 and the constant edge 02 (missing edge 12). These are
    actual input maps, not yet extended triangles or reverse cylinders.
    The nine-step Kan extension is a subsequent dependency. *)

(** * 三角初始区域上的实际相对数据

    初始区域包含整个空间边界与两条时间边，边界给定恒为基点常值。
    相对柱定律给出边界与边的一致；实际同伦端点方程通过
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.TimeOverlap.cylinder_time_factors_from_endpoints}
    {%[cylinder_time_factors_from_endpoints]%}% 给出共同时间相容。
    初始映射就是已构造的
    %\coqref{Cats.Instance.Set.Simplicial.TriangleInput.TriangleInputN}
    {%[TriangleInputN]%}%，无需重证下降。

    复合保留01、12边，缺02边；反向保留01边及常值02边，缺12边。
    这些是实际初始映射，尚非已延拓三角形或反向柱；九步Kan延拓留待依赖阶段。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\partial\Delta[2]\times\Delta[2] \arrow[r] \arrow[dr,"b"']
  & A_0 \arrow[d,dashed,"I"]
  & \Delta[2]\times\Lambda[2;r] \arrow[l] \arrow[dl,"H_j"] \\
& X &
\end{tikzcd}
\end{center}%
*)

(** ** Constant Boundary and Retained Relative Maps

    Fix independent carrier/equality bounds, X and a base vertex. Only
    retained edges are constrained; agreement witnesses are not identified. *)

(** ** 常值边界与保留的相对映射

    固定独立载体／相等界、X与基点；只约束保留边，不等同各相容见证。 *)

Section RelativeInput.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** The prescribed value ignores both spatial and parameter coordinates. *)

(** 给定值不依赖空间与参数坐标。 *)

Program Definition SphereTriangleBoundaryN
  : SimplicialParameterF (∂Δ[2]) 2 ⇒ X
  :=
  {|nt n := {|func z := simplex_constant X b n|}
  |}.
Next Obligation. intros x y E. reflexivity. Defined.
Next Obligation. intros x. symmetry. apply simplex_constant_restrict. Defined.

(** Relative laws supply precisely the boundary-edge overlap condition. *)

(** 相对定律恰好给出边界与边的交叠条件。 *)

Definition sphere_triangle_input_boundary_matching (r : Ordinal 2)
    (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j))
  : triangle_input_boundary_agreement r SphereTriangleBoundaryN H.
Proof. intros j Hj n a t. symmetry. exact (R j Hj n a t). Defined.

(** Glue the full initial region from retained relative maps and endpoints. *)

(** 由保留的相对映射与端点相容粘合整个初始区域。 *)

Definition SphereTriangleInputN (r : Ordinal 2)
    (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j))
    (E : cylinder_time_endpoint_matching r H)
  : TriangleHornStage r 0 ⇒ X
  := TriangleInputN r SphereTriangleBoundaryN H
      (sphere_triangle_input_boundary_matching r H R)
      (cylinder_time_factors_from_endpoints r H E).

(** Recover the prescribed value for every boundary and parameter simplex. *)

(** 对每个边界与参数单形恢复给定值。 *)

Definition sphere_triangle_input_boundary_β (r : Ordinal 2)
    (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j))
    (E : cylinder_time_endpoint_matching r H)
    n (a : (∂Δ[2]) n) (t : (Δ[2]) n)
  : SphereTriangleInputN r H R E n
      (triangle_input_generator r (inl (n; (a, t)))) ≈S
      simplex_constant X b n
  := triangle_input_boundary_β r SphereTriangleBoundaryN H
      (sphere_triangle_input_boundary_matching r H R)
      (cylinder_time_factors_from_endpoints r H E) n a t.

(** Recover every retained cylinder value, including degenerate time. *)

(** 恢复每个保留柱的取值，包括退化时间。 *)

Definition sphere_triangle_input_face_β (r : Ordinal 2)
    (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j))
    (E : cylinder_time_endpoint_matching r H)
    j (Hj : ¬ j = r) n z
  : SphereTriangleInputN r H R E n
      (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z
  := triangle_input_face_β r SphereTriangleBoundaryN H
      (sphere_triangle_input_boundary_matching r H R)
      (cylinder_time_factors_from_endpoints r H E) j Hj n z.

(** Compare independent relative/endpoint witnesses using only retained maps. *)

(** 只比较保留映射，允许相对及端点见证独立。 *)

Definition sphere_triangle_input_proper (r : Ordinal 2)
    (H K : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j))
    (S : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (K j))
    (E : cylinder_time_endpoint_matching r H)
    (F : cylinder_time_endpoint_matching r K)
    (G : ∀ j, ¬ j = r → H j ≈N K j)
  : SphereTriangleInputN r H R E ≈N SphereTriangleInputN r K S F.
Proof. apply triangle_input_proper; [reflexivity | exact G]. Defined.

End RelativeInput.

(** ** Inputs for Composition and Reversal

    Supply actual relative sphere cylinders. The omitted family's value
    is a harmless constant placeholder, never an additional constraint.
    Endpoint proofs use only the given cylinders' two endpoint laws. *)

(** ** 复合与反向的输入

    给定实际相对球面柱。缺边取一个常值占位，不施加额外条件；
    端点证明只使用给定柱自身的两个端点定律。 *)

Section CylinderInputs.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context {x y z : TwoSphereS X b}.

(** Retain H on 01 and K on 12; edge 02 is omitted. *)

(** 在01边保留H、12边保留K；缺02边。 *)

Definition SphereCompositeEdges
    (H : TwoSphereCylinderHomotopy X b x y)
    (K : TwoSphereCylinderHomotopy X b y z)
    (j : Ordinal 2)
  : SimplicialCylinderF (Δ[2]) ⇒ X.
Proof.
  destruct j as [[] | [[] | [[] | []]]].
  - exact (homotopy_map K.1).
  - exact (homotopy_map (SimplicialConstantHomotopy ⟦x.1⟧Δ[X; 2])).
  - exact (homotopy_map H.1).
Defined.

(** The two retained maps keep the whole spatial boundary fixed. *)

(** 两个保留映射固定整个空间边界。 *)

Definition sphere_composite_edges_relative
    (H : TwoSphereCylinderHomotopy X b x y)
    (K : TwoSphereCylinderHomotopy X b y z)
  : ∀ j, ¬ j = fin_first⁺ →
      is_two_sphere_cylinder_relative X b (SphereCompositeEdges H K j).
Proof.
  intros [[] | [[] | [[] | []]]] Hj.
  - exact K.2.
  - destruct (Hj eq_refl).
  - exact H.2.
Defined.

(** The final endpoint of H is the initial endpoint of K, in both orders. *)

(** H的终点是K的起点；两个有序交叠均满足条件。 *)

Definition sphere_composite_edges_endpoints
    (H : TwoSphereCylinderHomotopy X b x y)
    (K : TwoSphereCylinderHomotopy X b y z)
  : cylinder_time_endpoint_matching fin_first⁺ (SphereCompositeEdges H K).
Proof.
  intros [[] | [[] | [[] | []]]] [[] | [[] | [[] | []]]] Hj Hk E n a;
    try (destruct (Hj eq_refl)); try (destruct (Hk eq_refl));
    try (destruct (E eq_refl)).
  - transitivity (⟦y.1⟧Δ[X; 2] n a).
    + exact (simplicial_homotopy_0 K.1 n a).
    + symmetry. exact (simplicial_homotopy_1 H.1 n a).
  - transitivity (⟦y.1⟧Δ[X; 2] n a).
    + exact (simplicial_homotopy_1 H.1 n a).
    + symmetry. exact (simplicial_homotopy_0 K.1 n a).
Defined.

(** The actual zero-stage map required to extend two composable cylinders. *)

(** 延拓两个可复合柱所需的实际零阶段映射。 *)

Definition SphereCompositeTriangleInput
    (H : TwoSphereCylinderHomotopy X b x y)
    (K : TwoSphereCylinderHomotopy X b y z)
  : TriangleHornStage fin_first⁺ 0 ⇒ X
  := SphereTriangleInputN X b fin_first⁺ (SphereCompositeEdges H K)
      (sphere_composite_edges_relative H K)
      (sphere_composite_edges_endpoints H K).

(** Retain H on 01 and the constant at x on 02; edge 12 is omitted. *)

(** 在01边保留H、02边保留x处的常柱；缺12边。 *)

Definition SphereReverseEdges (H : TwoSphereCylinderHomotopy X b x y)
    (j : Ordinal 2)
  : SimplicialCylinderF (Δ[2]) ⇒ X.
Proof.
  destruct j as [[] | [[] | [[] | []]]].
  - exact (homotopy_map (SimplicialConstantHomotopy ⟦x.1⟧Δ[X; 2])).
  - exact (homotopy_map (SimplicialConstantHomotopy ⟦x.1⟧Δ[X; 2])).
  - exact (homotopy_map H.1).
Defined.

(** H and the supplied constant map satisfy the relative law. *)

(** H与给定常映射满足相对定律。 *)

Definition sphere_reverse_edges_relative
    (H : TwoSphereCylinderHomotopy X b x y)
  : ∀ j, ¬ j = fin_first →
      is_two_sphere_cylinder_relative X b (SphereReverseEdges H j).
Proof.
  intros [[] | [[] | [[] | []]]] Hj.
  - destruct (Hj eq_refl).
  - intros n a t. exact (two_sphere_boundary_constant X b x n a).
  - exact H.2.
Defined.

(** The two retained edges start at x; no reverse cylinder is presumed. *)

(** 两个保留边都起于x；不预设反向柱。 *)

Definition sphere_reverse_edges_endpoints
    (H : TwoSphereCylinderHomotopy X b x y)
  : cylinder_time_endpoint_matching fin_first (SphereReverseEdges H).
Proof.
  intros [[] | [[] | [[] | []]]] [[] | [[] | [[] | []]]] Hj Hk E n a;
    try (destruct (Hj eq_refl)); try (destruct (Hk eq_refl));
    try (destruct (E eq_refl)).
  - symmetry. exact (simplicial_homotopy_0 H.1 n a).
  - exact (simplicial_homotopy_0 H.1 n a).
Defined.

(** The actual zero-stage map from which a reverse may later be extended. *)

(** 可在后续延拓出反向柱的实际零阶段映射。 *)

Definition SphereReverseTriangleInput
    (H : TwoSphereCylinderHomotopy X b x y)
  : TriangleHornStage fin_first 0 ⇒ X
  := SphereTriangleInputN X b fin_first (SphereReverseEdges H)
      (sphere_reverse_edges_relative H) (sphere_reverse_edges_endpoints H).

End CylinderInputs.
