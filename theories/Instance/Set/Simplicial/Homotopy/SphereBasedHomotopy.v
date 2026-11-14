From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Set.Simplicial.Homotopy.SphereMap.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

Local Open Scope nat_scope.

(** * Restricting a Homotopy with Constant Base Trajectory

    A simplicial homotopy supplies an actual trajectory edge for every
    source vertex. Here only the trajectory of one chosen vertex b is
    required to agree with the constant edge at c. This is explicit
    specified equality of edges, not a rule replacing arbitrary paths
    by equality of vertices.

    Naturality makes every time simplex along b constant. Endpoint
    equations then derive f₀b ≈ c and g₀b ≈ c. The existing sphere maps
    and equal-base transports therefore land at that same target base.
    Precompose the original homotopy with the represented source sphere;
    its full relative boundary follows from the sphere boundary and the
    constant trajectory. The stored cylinder map remains this actual
    precomposition. No horn choice or algebraic structure is required.

    This extracts the argument used by the one-reduced special case:
    requiring every target edge to be constant is sufficient but stronger
    than controlling the single trajectory used here. *)

(** * 限制基点轨迹为常值的同伦

    单纯同伦为每个源顶点提供实际轨迹边。此处只要求一个选定顶点 b 的轨迹
    等于 c 处的常值边。这是显式的指定边相等，不是将任意路径替换为顶点相等
    的规则。

    自然性使沿 b 的每个时间单形均为常值，再由端点方程导出 f₀b ≈ c 和
    g₀b ≈ c。因此，既有球面映射及相等基点运输落在相同目标基点处。将原同伦
    与源球面所表示映射预复合，完整相对边界由球面边界及常值轨迹给出。
    保存的柱映射仍是这份实际预复合；不要求 horn 选择或代数结构。

    这里抽取了 one-reduced 特例使用的论证：每条目标边均为常值足够，但比
    此处只控制一条实际轨迹更强。 *)

(** The vertical arrow restricts both the spatial and time coordinates.
    The supplied edge equality makes the top-right edge constant; its
    restrictions give the corresponding constant n-simplices. *)

(** 竖箭头同时限制空间及时间坐标。给定边相等使右上轨迹边为常值，限制它
    得到相应常值 n-单形。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
(b_1,\operatorname{id}_{[1]}) \arrow[r,mapsto,"H_1"]
  \arrow[d,mapsto,"{\tau^*}"'] &
H_1(b_1,\operatorname{id}_{[1]}) \arrow[d,mapsto,"{\tau^*}"] \\
(b_n,\tau) \arrow[r,mapsto,"H_n"'] & c_n
\end{tikzcd}
\end{center}%
*)

(** ** One Explicit Constant Trajectory

    Fix independent ambient carrier/equality bounds, a homotopy and two
    base vertices. Only its actual trajectory edge is assumed constant;
    derive endpoint corrections rather than storing additional choices. *)

(** ** 一条显式常值轨迹

    固定独立环境载体／相等界、同伦及两个基点顶点。仅假设其实际轨迹边为
    常值，端点校正由此导出，不另存选择。 *)

Section BasedSphereHomotopy.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Y}.
Context (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0).
Context (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
    ≈S simplex_constant Y c 1).

(** All time shapes are restrictions of the supplied trajectory edge. *)

(** 全部时间形状都是给定轨迹边的限制。 *)

Lemma sphere_homotopy_trace (n : nat)
    (t : (Δ[1] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : homotopy_map H n (simplex_constant X b n, t) ≈S
      simplex_constant Y c n.
Proof.
  pose (τ := lower t).
  pose (z := (simplex_constant X b 1, simplex_generic 1)
    : SimplicialCylinderF X 1).
  transitivity (homotopy_map H n ((SimplicialCylinderF X)[τ]Δ z)).
  - apply func_proper. split.
    + symmetry. exact (simplex_constant_restrict X b τ).
    + refine {|lower := _
              |}. symmetry.
      change (@HomEq Δ n 1%nat (id ∘ τ) τ). apply comp_id_l.
  - transitivity (Y[τ]Δ (homotopy_map H 1 z)).
    + exact (simplex_restrict_natural (homotopy_map H) τ z).
    + transitivity (Y[τ]Δ (simplex_constant Y c 1)).
      * apply func_proper. exact E.
      * apply simplex_constant_restrict.
Defined.

(** Both image vertices agree with c by endpoint equations. No equality
    of their Type-valued witnesses is asserted. *)

(** 由端点方程，两个像顶点均与 c 相等；不声称其 Type 值见证相等。 *)

Lemma sphere_homotopy_base (t : bool)
  : (if t then g else f) 0 b ≈S c.
Proof.
  transitivity (homotopy_map H 0 (b, SimplicialIntervalPointN t 0 tt)).
  - symmetry. exact (homotopy_endpoint H t 0 b).
  - transitivity (homotopy_map H 0
      (simplex_constant X b 0, SimplicialIntervalPointN t 0 tt)).
    + apply func_proper. split.
      * symmetry. exact (simplex_constant_zero X b).
      * reflexivity.
    + transitivity (simplex_constant Y c 0).
      * apply sphere_homotopy_trace.
      * apply simplex_constant_zero.
Defined.

(** Restrict the original homotopy to the source sphere and correct its
    two image bases using the preceding derived equalities. *)

(** 将原同伦限制到源球面，再用前面导出的相等校正两个像基点。 *)

Definition SphereBasedHomotopyCylinder (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (two_sphere_change_base_resp Y (sphere_homotopy_base false)
        (two_sphere_map_resp f b x))
      (two_sphere_change_base_resp Y (sphere_homotopy_base true)
        (two_sphere_map_resp g b x)).
Proof.
  assert (Ef : (f ∘Nv ⟦x.1⟧Δ[X; 2]) ≈N ⟦f 2 x.1⟧Δ[Y; 2]).
  { intros n [θ]. exact (simplex_restrict_natural f θ x.1). }
  assert (Eg : (g ∘Nv ⟦x.1⟧Δ[X; 2]) ≈N ⟦g 2 x.1⟧Δ[Y; 2]).
  { intros n [θ]. exact (simplex_restrict_natural g θ x.1). }
  exists (HomotopyChangeEndpoints
    (SimplicialPreHomotopy H ⟦x.1⟧Δ[X; 2]) Ef Eg).
  intros n a t.
  change (homotopy_map H n (X[(lower a).1]Δ x.1, t) ≈S
    simplex_constant Y c n).
  transitivity (homotopy_map H n (simplex_constant X b n, t)).
  - apply func_proper. split.
    + apply two_sphere_boundary_constant.
    + reflexivity.
  - exact (sphere_homotopy_trace n t).
Defined.

End BasedSphereHomotopy.
