(** * From Unique Horns to Unique Boundaries

    This chapter follows the groupoid nerve construction. It assumes
    familiarity with simplices, faces and horns. The argument uses the
    general matching theory, rather than rebuilding labelled diagrams. *)

(** * 从唯一 horn 到唯一边界

    本章接续群胚 nerve 构造，假定读者熟悉单形、面与 horn。论证使用一般匹配
    理论，而不重新构造带标签的图式。 *)

From Cats Require Import
  Instance.Set.Simplicial.Coskeletal
  Instance.Set.Simplicial.Kan
  Instance.Bool.Nerve.

Local Open Scope nat_scope.

(** ** 1. A horn and a boundary ask different questions

    [BoundaryS X n] contains maps from the entire boundary [∂Δ[n]] to [X].
    Their face data include every compatibility on an overlap. A horn omits
    one face. Filling a horn therefore constructs both a top simplex and the
    missing face; filling a boundary must recover that face as well.

    Arbitrary Kan filling does not guarantee boundary filling. For example,
    a triangular boundary prescribes three edges that need not satisfy the
    composition equation of a categorical nerve. *)

(** ** 1. horn 与边界提出不同问题

    [BoundaryS X n] 包含从整个边界 [∂Δ[n]] 到 [X] 的映射，面数据包含每个
    交叠上的相容性。horn 则省略一个面。因此，填充 horn 同时构造顶维单形和
    缺失面；填充边界还必须恢复原先给定的那个面。

    任意 Kan 填充不保证边界可填充。例如，三角形边界指定的三条边未必满足
    范畴 nerve 的复合方程。 *)

Check @boundary_matching_iso.
Check @boundary_face_overlap.

(** ** 2. Recover the missing face from one lower dimension

    Start with a boundary of dimension [n + 2]. Forget face zero, fill the
    resulting horn, and call the simplex [x]. All retained faces of [x] are
    already correct. To check face zero, compare its own boundary with the
    boundary of the originally prescribed face.

    The shifted face equations and boundary overlap equations make these
    lower boundaries equal. Unique horn filling in dimension [n + 1]
    reflects this equality to the two faces themselves. Finally, uniqueness
    of the upper horn filler also gives uniqueness of the boundary filler.

    [boundary_from_horns_universal] formalizes this argument for any
    simplicial setoid, requiring unique filling only for the first horn in
    the two adjacent dimensions. All equalities are the specified setoid
    equalities; no equality of overlap proofs is used. *)

(** ** 2. 从低一维恢复缺失面

    从一个 [n + 2] 维边界出发，忘却零号面，填充所得 horn，并将单形记为 [x]。
    [x] 的全部保留面已经正确。为检查零号面，比较它自身的边界与原先指定面
    的边界。

    移位面方程和边界交叠方程保证这两个低维边界相等。[n + 1] 维的唯一 horn
    填充将此相等反映到两个面本身。最后，高维 horn 填充的唯一性也给出边界
    填充的唯一性。

    [boundary_from_horns_universal] 对任意单纯广集形式化此论证，只要求相邻两个
    维度的第一 horn 具有唯一填充。全部相等均为指定广集相等，不比较交叠证明。 *)

Check @boundary_reflects_from_horns.
Check @boundary_from_horns_universal.

(** ** 3. Coskeletality packages the unique boundary fibers

    [X ⦂ Cosk[k]] says that boundaries above dimension [k] have unique
    fillers. It retains the computational universal property at native
    value sizes. The index [n] in [fill∂[X; k; n]] is an offset: the filled
    dimension is [S (k + n)].

    Uniqueness makes filling respectful and gives beta and eta equations.
    After lifting into common size bounds, [coskeletal_boundary_iso] states
    that simplices and boundary maps are isomorphic setoids. It does not
    require the larger boundary-map setoid to fit in the native value size. *)

(** ** 3. 余骨架性组合唯一边界纤维

    [X ⦂ Cosk[k]] 表示高于 [k] 维的边界具有唯一填充，在原生值大小中保留可计算
    的泛性质。[fill∂[X; k; n]] 中的 [n] 是偏移量：填充维度为 [S (k + n)]。

    唯一性使填充保持相等，并给出 β 和 η 方程。提升到共同大小界后，
    [coskeletal_boundary_iso] 表示单形与边界映射是同构广集，不要求较大的边界
    映射广集落入原生值大小。 *)

Section Tetrahedron.
Context {X : Functor (Δ^op) SetCat} `{HX : !IsCoskeletal X 2}.

(** Filling four compatible triangular faces recovers the given boundary. *)

(** 填充四个相容的三角形面，恢复给定边界。 *)

Example tetrahedron_boundary (b : BoundaryS X 3)
  : (fill∂[X; 2; 0] b)↾∂[X; 3] ≈S b.
Proof. exact (coskeletal_fill_β 0 b). Defined.

(** Exercise: two tetrahedra with equal boundaries are equal. Use eta to
    reconstruct them, and respectfulness to compare the reconstructed values. *)

(** 练习：具有相等边界的两个四面体相等。用 η 重构它们，再用保相等性比较重构值。 *)

Example tetrahedron_extensionality (x y : X 3)
    (E : x↾∂[X; 3] ≈S y↾∂[X; 3])
  : x ≈S y.
Proof.
  transitivity (fill∂[X; 2; 0] (x↾∂[X; 3])).
  - symmetry. exact (coskeletal_fill_η 0 x).
  - transitivity (fill∂[X; 2; 0] (y↾∂[X; 3])).
    + exact (@func_proper _ _ (fill∂[X; 2; 0]) _ _ E).
    + exact (coskeletal_fill_η 0 y).
Defined.

End Tetrahedron.

(** ** 4. Apply the theorem to groupoid nerves

    A groupoid vertex nerve has unique horn fillers in every dimension at
    least two. Applying the general theorem in successive dimensions proves
    [vertex_groupoid_IsCoskeletal]. The boolean model specializes this result
    without identifying its two different loops.

    Thus higher simplices of these nerves contain no additional independent
    boundary-filling data above dimension two. This does not construct a
    genuinely higher Kan example, nor prove coskeletality for nerves of
    arbitrary categories or full faithfulness of the nerve construction. *)

(** ** 4. 应用于群胚 nerve

    群胚顶点 nerve 在全部至少二维的情形具有唯一 horn 填充。对相邻维度应用一般
    定理即得 [vertex_groupoid_IsCoskeletal]。布尔模型特化此结果，其两条不同环路
    仍未被等同。

    因而这些 nerve 的高维单形在二维以上不含额外独立的边界填充数据。这没有构造
    真正高阶的 Kan 例子，也没有证明任意范畴 nerve 的余骨架性或 nerve 构造的全忠实性。 *)

Check @vertex_groupoid_IsCoskeletal.
Check BoolVertexNerve_IsCoskeletal.
Check bool_vertex_loop_not_id.
