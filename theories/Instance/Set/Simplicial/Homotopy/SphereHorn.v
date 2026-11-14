From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereMap
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Set.Simplicial.Matching.
From Cats Require Import
  Cat.Core.
From Stdlib Require Import
  Arith.PeanoNat.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Gluing Based Spheres into Actual Tetrahedron Horns

    Based triangles have the same constant boundary, so they agree wherever
    distinct tetrahedron faces meet. The existing matching descent from
    %\coqref{Cats.Instance.Set.Simplicial.Matching.HornMatchingS}
    {%[HornMatchingS]%}% turns these values into a map from the actual horn.
    It includes all degrees and degeneracies, not just a list of three faces.

    A selected filler supplies the omitted triangle. Its boundary is again
    constant, since each of its edges also lies in a retained sphere face.
    This constructs sphere representatives and actual tetrahedra. It does
    not yet prove that different fillers give equal generated classes, or
    that their choices define a group operation on classes. *)

(** * 将基点球面粘成实际四面体 Horn

    基点三角形具有相同的常值边界，所以在不同四面体面的交叠处一致。既有
    %\coqref{Cats.Instance.Set.Simplicial.Matching.HornMatchingS}
    {%[HornMatchingS]%}% 匹配下降将这些值转为从实际 horn 出发的映射，
    包含所有维度及退化，而不仅是三个面的列表。

    选定填充给出缺失三角形。它的每条边也处于一个保留球面面中，因而边界仍为
    常值。由此构造球面代表及实际四面体；尚未证明不同填充给出相等生成类，
    也未证明这些选择定义类上的群运算。 *)

(** ** Sphere Values Agree on Intersections

    Fix independent ambient sizes, a simplicial setoid and a base vertex.
    Distinct cofaces force a common factor to omit a vertex inside each
    triangle. Reuse the full boundary-constant lemma for that factor. *)

(** ** 球面值在交叠处一致

    固定独立环境大小、单纯广集及基点顶点。不同余面使共同因子在各三角形内
    省略一个顶点；对该因子复用完整边界常值引理。 *)

Section SphereHornMatching.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** A common factor of distinct faces lies in the sphere's boundary. *)

(** 不同面的共同因子处于球面边界中。 *)

Lemma two_sphere_face_intersection (j k : Ordinal 3) (Hjk : ¬ j = k)
    {n : nat} (f g : (@Hom Δ) n 2%nat)
    (E : δ[2; j] ∘ f ≈ δ[2; k] ∘ g) (x : TwoSphereS X b)
  : X[f]Δ x.1 ≈S simplex_constant X b n.
Proof.
  pose (v := @fin_unskip 3 j k (λ F, Hjk (symmetry F))).
  assert (Hf : ∀ z, ¬ f z = v.1).
  { intros z F. apply (@fin_skip_avoids 3 k (g z)).
    change (δ[2; k] (g z) = k).
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    change (δ[2; j] (f z) = δ[2; k] (g z)) in Ez.
    rewrite <- Ez, F. exact v.2. }
  exact (two_sphere_boundary_constant X b x n
    {|lower := (f; boundary_member_of_omission v.1 f Hf)
    |}).
Defined.

(** Matching data assign a sphere to each retained face. The entry at the
    omitted index is ignored; no boundary filler is supplied by that entry. *)

(** 匹配数据给每个保留面赋予一个球面。缺失索引处的项被忽略，不以该项给出
    边界填充。 *)

Program Definition SphereTetrahedronMatching (i : Ordinal 3)
    (a : Ordinal 3 → TwoSphereS X b)
  : HornMatchingS X 2 i
  :=
  {|matching_value j := (a j.1).1
  |}.
Next Obligation.
  destruct j as [k Hk], i0 as [j Hj].
  destruct (Nat.eq_dec (@fin_rank 4 j) (@fin_rank 4 k)) as [F | F].
  - pose proof (@fin_rank_injective 4 j k F) as G. subst k.
    apply simplex_restrict_proper.
    apply (snd (simplex_eq_iff _ _)). intros z.
    apply (@fin_skip_injective 3 j).
    exact (fst (simplex_eq_iff _ _) E z).
  - assert (Hjk : ¬ j = k) by (intros G; subst k; destruct (F eq_refl)).
    transitivity (simplex_constant X b X0).
    + exact (two_sphere_face_intersection j k Hjk f h E (a j)).
    + symmetry. exact (two_sphere_face_intersection k j
        (λ G, Hjk (symmetry G)) h f (symmetry E) (a k)).
Defined.

(** Descend through the existing generated-sieve construction, retaining
    the actual face factorization of every horn simplex. *)

(** 经既有生成筛构造下降，保留每个 horn 单形的实际面分解。 *)

Definition SphereTetrahedronHornN (i : Ordinal 3)
    (a : Ordinal 3 → TwoSphereS X b)
  : HornS X 3 i
  := SieveMatchingN _ _ (SphereTetrahedronMatching i a).

(** Every retained face recovers the prescribed triangle in specified
    equality. The retained-face proof is not compared. *)

(** 每个保留面按指定相等恢复给定三角形，不比较保留面证明。 *)

Lemma sphere_tetrahedron_horn_face (i : Ordinal 3)
    (a : Ordinal 3 → TwoSphereS X b) (j : Ordinal 3) (Hj : ¬ j = i)
  : face[i; j; Hj] (SphereTetrahedronHornN i a) ≈S (a j).1.
Proof. apply simplex_restrict_id. Defined.

End SphereHornMatching.

(** ** The Other Face Containing an Edge

    In a tetrahedron, an edge of face j also lies in another face k.
    Both indices and the local edge index are computed with finite skips;
    only these concrete ordinal positions use native equality. *)

(** ** 包含一条边的另一个面

    在四面体中，面 j 的一条边也处于另一个面 k 中。两个索引及局部边索引均
    通过有限跳过运算计算；仅这些具体序数位置使用原生相等。 *)

Definition tetrahedron_face_partner (j : Ordinal 3) (e : Ordinal 2)
  : Ordinal 3
  := δ[2; j] e.

(** The other face is distinct from the original one. *)

(** 另一个面与原面不同。 *)

Definition tetrahedron_face_partner_distinct (j : Ordinal 3) (e : Ordinal 2)
  : ¬ tetrahedron_face_partner j e = j
  := @fin_skip_avoids 3 j e.

(** Locate the original omitted vertex inside its partner face. *)

(** 将原来省略的顶点定位于对应的另一个面内部。 *)

Definition tetrahedron_edge_partner (j : Ordinal 3) (e : Ordinal 2)
  : Ordinal 2
  := (@fin_unskip 3 (tetrahedron_face_partner j e) j
      (λ F, tetrahedron_face_partner_distinct j e (symmetry F))).1.

(** The two face-edge routes select exactly the same ordered edge. *)

(** 两条先取面再取边的路径选取完全相同的有序边。 *)

Lemma tetrahedron_face_edge_swap (j : Ordinal 3) (e : Ordinal 2)
  : δ[2; j] ∘ δ[1; e] ≈
      δ[2; tetrahedron_face_partner j e] ∘
        δ[1; tetrahedron_edge_partner j e].
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  destruct j as [[] | [[] | [[] | [[] | []]]]],
    e as [[] | [[] | [[] | []]]], z as [[] | [[] | []]]; reflexivity.
Defined.

(** ** Reading a Filler's Omitted Sphere

    Fix a base vertex and a family of based triangles. Any actual filler
    of their horn has a based triangle as its omitted face. Only after
    this proof do we consume chosen fillers. *)

(** ** 读出填充的缺失球面

    固定基点顶点及一族基点三角形。其 horn 的任意实际填充，都以一个基点
    三角形作为缺失面。证明此性质之后才消费选定填充。 *)

Section SphereHornFillers.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** A filler recovers every prescribed retained triangle. *)

(** 填充恢复每个给定保留三角形。 *)

Lemma sphere_tetrahedron_filler_face (i : Ordinal 3)
    (a : Ordinal 3 → TwoSphereS X b) (w : X 3)
    (H : is_horn_filler (SphereTetrahedronHornN X b i a) w)
    (j : Ordinal 3) (Hj : ¬ j = i)
  : d[X; 2; j] w ≈S (a j).1.
Proof.
  transitivity (face[i; j; Hj] (SphereTetrahedronHornN X b i a)).
  - exact (fst (horn_filler_faces_iff _ w) H j Hj).
  - apply sphere_tetrahedron_horn_face.
Defined.

(** Each edge of the omitted face is an edge of a retained sphere. *)

(** 缺失面的每条边均为一个保留球面的边。 *)

Lemma sphere_tetrahedron_missing_boundary (i : Ordinal 3)
    (a : Ordinal 3 → TwoSphereS X b) (w : X 3)
    (H : is_horn_filler (SphereTetrahedronHornN X b i a) w)
    (e : Ordinal 2)
  : d[X; 1; e] (d[X; 2; i] w) ≈S simplex_constant X b 1.
Proof.
  transitivity (X[δ[2; i] ∘ δ[1; e]]Δ w).
  - symmetry. apply simplex_restrict_comp.
  - transitivity (X[δ[2; tetrahedron_face_partner i e] ∘
      δ[1; tetrahedron_edge_partner i e]]Δ w).
    + apply simplex_restrict_proper. apply tetrahedron_face_edge_swap.
    + transitivity (d[X; 1; tetrahedron_edge_partner i e]
        (d[X; 2; tetrahedron_face_partner i e] w)).
      * apply simplex_restrict_comp.
      * transitivity (d[X; 1; tetrahedron_edge_partner i e]
          (a (tetrahedron_face_partner i e)).1).
        -- apply func_proper. exact (sphere_tetrahedron_filler_face i a w H
             _ (tetrahedron_face_partner_distinct i e)).
        -- exact ((a (tetrahedron_face_partner i e)).2 _).
Defined.

(** Retain the omitted triangle and the boundary equations just proved. *)

(** 保留缺失三角形及刚证明的边界方程。 *)

Definition sphere_tetrahedron_missing_sphere (i : Ordinal 3)
    (a : Ordinal 3 → TwoSphereS X b) (w : X 3)
    (H : is_horn_filler (SphereTetrahedronHornN X b i a) w)
  : TwoSphereS X b
  := (d[X; 2; i] w; sphere_tetrahedron_missing_boundary i a w H).

(** Choose exactly one needed three-dimensional horn filler. No law says
    that the choice respects equality or agrees with another choice. *)

(** 仅选择所需的一个三维 horn 填充；不预设此选择保持相等或与另一选择一致。 *)

Definition SphereTetrahedronFill (i : Ordinal 3)
    `{HX : !HasHornFillers X 3 i} (a : Ordinal 3 → TwoSphereS X b)
  : ∃ w : X 3, is_horn_filler (SphereTetrahedronHornN X b i a) w
  := horn_fill (SphereTetrahedronHornN X b i a).

(** The chosen omitted sphere retains the selected filler as its source. *)

(** 所选缺失球面保留选定填充作为其来源。 *)

Definition SphereTetrahedronMissing (i : Ordinal 3)
    `{HX : !HasHornFillers X 3 i} (a : Ordinal 3 → TwoSphereS X b)
  : TwoSphereS X b
  := sphere_tetrahedron_missing_sphere i a
      (SphereTetrahedronFill i a).1 (SphereTetrahedronFill i a).2.

End SphereHornFillers.
