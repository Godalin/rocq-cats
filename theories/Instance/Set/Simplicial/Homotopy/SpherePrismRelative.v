From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Set.Simplicial.PrismGluing
  Cat.Shape.Simplex.PrismBoundary.
From Cats Require Import
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Reconstructing the Whole Relative Boundary

    Merely keeping endpoint triangles fixed does not make a cylinder
    relative to its boundary. Each spatial edge has two staircase
    triangles. The six side-face equations below detect the complete
    boundary law, including arbitrary time simplices and degeneracies.
    The proof uses the edge-cylinder cover, then reuses actual triangle
    gluing; it does not select Kan fillers. *)

(** * 重构整个相对边界

    仅固定端点三角形不能使柱相对于边界保持常值。每条空间边有两个阶梯
    三角形；下方六个侧面方程判定完整边界定律，包括任意时间单形和退化。
    证明使用边柱覆盖，再复用实际三角柱粘合，不选择 Kan 填充。 *)

(** For spatial edge j and staircase k, let (i,l) be the computed side
    pair. The square commutes in both shape coordinates. Constancy on
    these six triangles propagates along every edge-cylinder factor. *)

(** 对空间边 j 与阶梯 k，以 (i,l) 表示计算所得侧面二元组。方图的两个形状
    坐标均交换；这六个三角形上的常值沿每个边柱因子传播。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\Delta[2] \arrow[r,"{\delta_l}"]
  \arrow[d,"{(\sigma_k,T_k)}"']
  & \Delta[3] \arrow[d,"{(\sigma_i,T_i)}"] \\
\Delta[1]\times\Delta[1] \arrow[r,"{\delta_j\times1}"']
  & \Delta[2]\times\Delta[1] \arrow[r,dashed,"G"] & X
\end{tikzcd}
\end{center}%
*)

(** ** Detecting the Boundary of an Actual Map

    Fix independent value sizes, a target and a base vertex. The map is
    arbitrary; no endpoint or horn assumptions are needed for the criterion. *)

(** ** 判定实际映射的边界

    固定独立取值大小、目标及基点。映射任意；此判据不要求端点或 horn 假设。 *)

Section RelativeBoundary.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialCylinderF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

(** Read one staircase of the cylinder on a spatial boundary edge. *)

(** 读取一条空间边界边之柱上的一块阶梯。 *)

Definition two_sphere_boundary_prism_value (K : Q ⇒ X)
    (j : Ordinal 2) (k : Ordinal 1)
  : X 2
  := K 2 ({|lower := δ[1; j] ∘ σ[1; k]|},
          {|lower := SimplexPrismTimeF k|}).

(** Six values detect the full all-degree boundary law. Restrict the
    time coordinate along the same computed factor as the spatial edge. *)

(** 六个值判定每维的完整边界定律；时间坐标须沿空间边所用的同一计算因子限制。 *)

Definition two_sphere_cylinder_relative_iff (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      ∀ j k, two_sphere_boundary_prism_value K j k ≈S
        simplex_constant X b 2.
Proof.
  split.
  - intros H j k.
    exact (H 2 {|lower := (δ[1; j] ∘ σ[1; k];
      sieve_precomp (BoundarySieve 2) δ[1; j] σ[1; k]
        (boundary_face_member j))|} {|lower := SimplexPrismTimeF k|}).
  - intros H n [[a [j [f E]]]] [t].
    destruct (SimplexPrismFactor f t) as [k [h [F G]]].
    transitivity (K n
      ({|lower := (δ[1; j] ∘ σ[1; k]) ∘ h|},
       {|lower := SimplexPrismTimeF k ∘ h|})).
    + apply func_proper. split; refine {|lower := _|}.
      * transitivity (δ[1; j] ∘ f); [exact E |].
        transitivity (δ[1; j] ∘ (σ[1; k] ∘ h)).
        -- apply comp_proper; [reflexivity | symmetry; exact F].
        -- symmetry. apply comp_assoc.
      * symmetry. exact G.
    + transitivity (X[h]Δ (two_sphere_boundary_prism_value K j k)).
      * exact (simplex_restrict_natural K h
          ({|lower := δ[1; j] ∘ σ[1; k]|},
           {|lower := SimplexPrismTimeF k|})).
      * transitivity (X[h]Δ (simplex_constant X b 2)).
        -- apply func_proper. exact (H j k).
        -- apply simplex_constant_restrict.
Defined.

(** The indicated outer coface and boundary-edge staircase are the same
    actual simplex of the product, in both specified coordinates. *)

(** 所示外侧余面与边界边阶梯是积中同一个实际单形，两个坐标均按指定相等比较。 *)

Lemma two_sphere_boundary_prism_face (K : Q ⇒ X)
    (j : Ordinal 2) (k : Ordinal 1)
  : two_sphere_boundary_prism_value K j k ≈S
      d[X; 2; snd (simplex_triangle_prism_side j k)]
        (simplex_prism_eval K (fst (simplex_triangle_prism_side j k))).
Proof.
  transitivity (K 2
    ({|lower := σ[2; fst (simplex_triangle_prism_side j k)] ∘
        δ[2; snd (simplex_triangle_prism_side j k)]|},
     {|lower := SimplexPrismTimeF (fst (simplex_triangle_prism_side j k)) ∘
        δ[2; snd (simplex_triangle_prism_side j k)]|})).
  - apply func_proper. split; refine {|lower := _|}; symmetry.
    + apply simplex_triangle_prism_side_space.
    + apply simplex_triangle_prism_side_time.
  - exact (simplex_restrict_natural K
      δ[2; snd (simplex_triangle_prism_side j k)]
      (simplex_prism_generator 2 (fst (simplex_triangle_prism_side j k)))).
Defined.

(** A finite relative condition for three supplied tetrahedra. It contains
    exactly the six external faces, not endpoints or the shared diagonals. *)

(** 三个给定四面体的有限相对条件；恰好包含六个外侧面，不包含端点或共享对角面。 *)

Definition is_two_sphere_prism_relative (a : Ordinal 2 → X 3)
  : Type
  := ∀ j k, d[X; 2; snd (simplex_triangle_prism_side j k)]
      (a (fst (simplex_triangle_prism_side j k))) ≈S simplex_constant X b 2.

(** The six outer faces of an actual map are constant exactly when its
    whole boundary cylinder is constant. *)

(** 实际映射的六个外侧面为常值，当且仅当其整个边界柱为常值。 *)

Definition two_sphere_prism_relative_iff (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      is_two_sphere_prism_relative (λ i, simplex_prism_eval K i).
Proof.
  split.
  - intros H j k.
    transitivity (two_sphere_boundary_prism_value K j k).
    + symmetry. apply two_sphere_boundary_prism_face.
    + exact (fst (two_sphere_cylinder_relative_iff K) H j k).
  - intros H. apply (snd (two_sphere_cylinder_relative_iff K)).
    intros j k. transitivity
      (d[X; 2; snd (simplex_triangle_prism_side j k)]
        (simplex_prism_eval K (fst (simplex_triangle_prism_side j k)))).
    + apply two_sphere_boundary_prism_face.
    + exact (H j k).
Defined.

(** Pointwise equal tetrahedra give equivalent finite relative conditions;
    side-equation witnesses are transported, not compared. *)

(** 逐点相等的四面体给出等价的有限相对条件；运输侧面方程见证，不比较它们。 *)

Definition two_sphere_prism_relative_resp (a a' : Ordinal 2 → X 3)
    (E : ∀ i, a i ≈S a' i)
  : is_two_sphere_prism_relative a ↔ is_two_sphere_prism_relative a'.
Proof.
  split; intros H j k.
  - transitivity (d[X; 2; snd (simplex_triangle_prism_side j k)]
      (a (fst (simplex_triangle_prism_side j k)))).
    + apply func_proper. symmetry. apply E.
    + exact (H j k).
  - transitivity (d[X; 2; snd (simplex_triangle_prism_side j k)]
      (a' (fst (simplex_triangle_prism_side j k)))).
    + apply func_proper. apply E.
    + exact (H j k).
Defined.

End RelativeBoundary.

(** ** The Two Endpoint Faces

    For an arbitrary target and cylinder map, time zero is the last
    face of the last prism piece; time one is the first face of the first
    piece. This identifies endpoints without a relative-boundary hypothesis. *)

(** ** 两个端点面

    对任意目标及柱映射，时间零是最后一块的最后面；时间一是第一块的第一面。
    判定端点不需要相对边界假设。 *)

Section PrismEndpoints.
Universes u p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.

Let D
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[2].

(** Evaluation of the endpoint map is the corresponding outer face. *)

(** 端点映射的求值就是相应的外面。 *)

Lemma simplex_triangle_prism_endpoint (K : SimplicialCylinderF D ⇒ X)
    (t : bool)
  : simplex_element_resp (K ∘Nv SimplicialEndpointN D t) ≈S
      if t then d[X; 2; fin_first] (simplex_prism_eval K fin_first)
      else d[X; 2; fin_first⁺⁺⁺] (simplex_prism_eval K fin_first⁺⁺).
Proof.
  destruct t.
  - change (K 2 ({|lower := (id : (@Hom Δ) 2 2)|},
      {|lower := ConstF [Ord 2] (C := [Ord 1]) fin_first⁺|}) ≈S
      d[X; 2; fin_first] (simplex_prism_eval K fin_first)).
    transitivity (K 2
      ({|lower := σ[2; fin_first] ∘ δ[2; fin_first]|},
       {|lower := SimplexPrismTimeF fin_first ∘ δ[2; fin_first]|})).
    + apply func_proper. split; refine {|lower := _|};
        apply (snd (simplex_eq_iff _ _)); intros i;
        destruct i as [[] | [[] | [[] | []]]]; reflexivity.
    + exact (simplex_restrict_natural K δ[2; fin_first]
        (simplex_prism_generator 2 fin_first)).
  - change (K 2 ({|lower := (id : (@Hom Δ) 2 2)|},
      {|lower := ConstF [Ord 2] (C := [Ord 1]) fin_first|}) ≈S
      d[X; 2; fin_first⁺⁺⁺] (simplex_prism_eval K fin_first⁺⁺)).
    transitivity (K 2
      ({|lower := σ[2; fin_first⁺⁺] ∘ δ[2; fin_first⁺⁺⁺]|},
       {|lower := SimplexPrismTimeF fin_first⁺⁺ ∘ δ[2; fin_first⁺⁺⁺]|})).
    + apply func_proper. split; refine {|lower := _|};
        apply (snd (simplex_eq_iff _ _)); intros i;
        destruct i as [[] | [[] | [[] | []]]]; reflexivity.
    + exact (simplex_restrict_natural K δ[2; fin_first⁺⁺⁺]
        (simplex_prism_generator 2 fin_first⁺⁺)).
Defined.

End PrismEndpoints.

(** ** Relative Reconstruction from Supplied Prism Values

    Fix three tetrahedra, the two shared-face equations and the six
    constant side faces. Endpoint equations are supplied separately.
    All maps reuse the same already integrated triangle gluing. *)

(** ** 从给定棱柱值作相对重构

    固定三个四面体、两个共享面方程及六个常值侧面；端点方程另行给定。
    全部映射复用同一份已集成三角柱粘合。 *)

Section RelativePrismGluing.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (a : Ordinal 2 → X 3).
Context (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
  d[X; 2; fin_first⁺] (a fin_first⁺)).
Context (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
  d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺)).

(** The six equations are necessary and sufficient for the glued map's
    entire relative boundary, independently of the shared-face witnesses. *)

(** 六个方程是粘合映射整个相对边界的充要条件，与共享面见证无关。 *)

Definition two_sphere_prism_gluing_relative_iff
  : is_two_sphere_cylinder_relative X b
      (SimplexTrianglePrismGluingN a H0 H1) ↔ is_two_sphere_prism_relative X b a.
Proof.
  split.
  - intros H j k. transitivity
      (d[X; 2; snd (simplex_triangle_prism_side j k)]
        (simplex_prism_eval (SimplexTrianglePrismGluingN a H0 H1)
          (fst (simplex_triangle_prism_side j k)))).
    + apply func_proper. symmetry. apply simplex_triangle_prism_gluing_β.
    + exact (fst (two_sphere_prism_relative_iff X b _) H j k).
  - intros H. apply (snd (two_sphere_prism_relative_iff X b _)).
    intros j k. transitivity
      (d[X; 2; snd (simplex_triangle_prism_side j k)]
        (a (fst (simplex_triangle_prism_side j k)))).
    + apply func_proper. apply simplex_triangle_prism_gluing_β.
    + exact (H j k).
Defined.

(** Two outer face equations give an actual homotopy with the same
    underlying glued map. Yoneda propagates generic endpoint evaluation. *)

(** 两个外面方程给出实际同伦，保留同一粘合映射；Yoneda 将泛端点求值传播到全映射。 *)

Program Definition SpherePrismHomotopy (x y : TwoSphereS X b)
    (E0 : d[X; 2; fin_first⁺⁺⁺] (a fin_first⁺⁺) ≈S x.1)
    (E1 : d[X; 2; fin_first] (a fin_first) ≈S y.1)
  : SimplicialHomotopy ⟦x.1⟧Δ[X; 2] ⟦y.1⟧Δ[X; 2]
  :=
  {|homotopy_map := SimplexTrianglePrismGluingN a H0 H1
  |}.
Next Obligation.
  change (Ordinal 2 → X 3) in a.
  apply (snd (simplex_map_unique _ _)).
  transitivity (if b0 then d[X; 2; fin_first] (a fin_first)
    else d[X; 2; fin_first⁺⁺⁺] (a fin_first⁺⁺)).
  - transitivity (if b0 then d[X; 2; fin_first]
      (simplex_prism_eval (SimplexTrianglePrismGluingN a H0 H1) fin_first)
      else d[X; 2; fin_first⁺⁺⁺]
        (simplex_prism_eval (SimplexTrianglePrismGluingN a H0 H1) fin_first⁺⁺)).
    + exact (simplex_triangle_prism_endpoint _ b0).
    + destruct b0; apply func_proper; apply simplex_triangle_prism_gluing_β.
  - destruct b0.
    + transitivity y.1; [exact E1 | symmetry; apply simplex_element_β].
    + transitivity x.1; [exact E0 | symmetry; apply simplex_element_β].
Defined.

(** The finite side equations reconstruct the complete relative cylinder,
    not merely its endpoints or its vertex trajectories. *)

(** 有限侧面方程重构完整相对柱，而非仅重构端点或顶点轨迹。 *)

Definition SpherePrismCylinder (x y : TwoSphereS X b)
    (E0 : d[X; 2; fin_first⁺⁺⁺] (a fin_first⁺⁺) ≈S x.1)
    (E1 : d[X; 2; fin_first] (a fin_first) ≈S y.1)
    (R : is_two_sphere_prism_relative X b a)
  : TwoSphereCylinderHomotopy X b x y
  := (SpherePrismHomotopy x y E0 E1;
      snd two_sphere_prism_gluing_relative_iff R).

End RelativePrismGluing.

(** ** Reading and Reconstructing a Relative Cylinder

    For a supplied full relative cylinder, extract the same three values,
    their common/side faces and endpoints. Reconstruction keeps those data
    and recovers the underlying map in specified natural equality. *)

(** ** 读取并重构相对柱

    对给定完整相对柱，提取同三个值、公共面、侧面和端点；重构保留这些数据，
    并按指定自然相等恢复底层映射。 *)

Section RelativePrismRecovery.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context {x y : TwoSphereS X b} (H : TwoSphereCylinderHomotopy X b x y).

Let K
  : SimplicialCylinderF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X
  := homotopy_map H.1.

(** The recovered witness has the same endpoints, with freshly derived
    endpoint and relative proofs. No equality of these proofs is claimed. *)

(** 恢复的见证具有原端点，端点及相对证明重新导出；不声称这些证明相等。 *)

Definition SpherePrismReconstruct
  : TwoSphereCylinderHomotopy X b x y.
Proof.
  refine (SpherePrismCylinder X b (λ i, simplex_prism_eval K i)
    (simplex_prism_values_adjacent K fin_first)
    (simplex_prism_values_adjacent K fin_first⁺) x y _ _ _).
  - transitivity (simplex_element_resp
      (K ∘Nv SimplicialEndpointN (Δ[2]) false)).
    + symmetry. exact (simplex_triangle_prism_endpoint K false).
    + transitivity (simplex_element_resp ⟦x.1⟧Δ[X; 2]).
      * exact (simplicial_homotopy_0 H.1 2 (simplex_generic 2)).
      * apply simplex_element_β.
  - transitivity (simplex_element_resp
      (K ∘Nv SimplicialEndpointN (Δ[2]) true)).
    + symmetry. exact (simplex_triangle_prism_endpoint K true).
    + transitivity (simplex_element_resp ⟦y.1⟧Δ[X; 2]).
      * exact (simplicial_homotopy_1 H.1 2 (simplex_generic 2)).
      * apply simplex_element_β.
  - exact (fst (two_sphere_prism_relative_iff X b K) H.2).
Defined.

(** The round trip compares only the existing underlying maps. *)

(** 往返只比较既有底层映射。 *)

Lemma two_sphere_prism_reconstruct_map
  : homotopy_map SpherePrismReconstruct.1 ≈N homotopy_map H.1.
Proof. exact (simplex_triangle_prism_gluing_η K). Defined.

End RelativePrismRecovery.
