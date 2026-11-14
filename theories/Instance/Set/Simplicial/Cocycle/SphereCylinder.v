From Cats Require Export
  Instance.Set.Simplicial.Cocycle.SphereGroup
  Instance.Set.Simplicial.Homotopy.SphereCylinder.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope monoid_scope.

(** * Comparing Cocycle Sphere Classes with Relative Cylinders

    The earlier generated relation used actual elementary tetrahedra.
    A relative cylinder instead supplies a whole map on [Δ[2] × Δ[1]],
    constant on its boundary throughout time. The three tetrahedra from
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two sphere prism faces}
    {%[two_sphere_prism_faces]%}% reduce its coefficient calculation to
    three applications of the existing cocycle tetrahedron equation.
    The two diagonal coefficients agree successively with the endpoints.

    Conversely, the coefficient classification already reflects equality
    of triangles in this particular model. A constant cylinder therefore
    gives an actual relative homotopy whenever the generated classes agree.
    This proves the two presentations equivalent in the cocycle model.
    It is not a theorem about arbitrary Kan objects or about invariance
    under unpointed homotopy equivalences. *)

(** * 比较 Cocycle 球面类与相对柱

    先前的生成关系使用实际初等四面体；相对柱则给出 [Δ[2] × Δ[1]] 上的
    完整映射，并在整个时间中保持边界常值。由
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two sphere prism faces}
    {%[two_sphere_prism_faces]%}%，三个四面体将系数计算归结为三次应用
    既有 cocycle 四面体方程。两个对角面系数依次与端点系数相等。

    反之，在这个具体模型中，系数分类已经能反映三角形相等。因此，若生成类
    相等，常值柱就给出实际相对同伦。由此证明 cocycle 模型中两个呈现等价；
    此结论并非任意 Kan 对象的定理，也未证明非基点同伦等价下的不变性。 *)

(** The equalities in the diagram live in the coefficient setoid.
    [D001] and [D011] are the two internal triangles, and each equality
    follows from one actual prism tetrahedron after its side faces are
    set to the unit. No cancellation or inverse is required. *)

(** 图中相等处于系数广集中。[D001]、[D011] 为两个内部三角形；每个相等都由
    一份实际棱柱四面体方程在侧面取单位后得到，不要求消去律或逆。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large]
c(x) \arrow[r,equal,"{w_2}"] & c(D_{001})
  \arrow[r,equal,"{w_1}"] & c(D_{011}) \arrow[r,equal,"{w_0}"] & c(y)
\end{tikzcd}
\end{center}%
*)

(** ** Three Tetrahedron Equations

    Fix only a coefficient monoid, and independent ambient simplex sizes.
    Neither inverses nor commutativity nor a selected Kan filler is needed
    for this comparison. *)

(** ** 三份四面体方程

    只固定系数幺半群及独立环境单形大小。此比较不需要逆、交换性或选定
    Kan 填充。 *)

Section CocycleCylinderComparison.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}.

Let Z
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

Let Q
  : SetC
  := TwoSphereClassS Z (two_cocycle_simplex_unit 0).

(** Every full relative cylinder preserves the coefficient. The proof
    inspects its three actual tetrahedra, not just its endpoint triangles. *)

(** 每份完整相对柱均保持系数。证明检查它的三个实际四面体，而非仅查看端点
    三角形。 *)

Lemma cocycle_two_sphere_cylinder_value
    (x y : TwoSphereS Z (two_cocycle_simplex_unit 0))
    (H : TwoSphereCylinderHomotopy Z (two_cocycle_simplex_unit 0) x y)
  : cocycle_two_sphere_value_resp x ≈S cocycle_two_sphere_value_resp y.
Proof.
  pose (v := (two_cocycle_triangle_value_resp : Z 2 →r M)).
  pose (a := two_sphere_cylinder_diagonal H fin_first).
  pose (b := two_sphere_cylinder_diagonal H fin_first⁺).
  assert (E : ∀ i : Ordinal 2,
    v (d[Z; 2; fin_first⁺⁺⁺] (two_sphere_prism H i)) ⋅
      v (d[Z; 2; fin_first⁺] (two_sphere_prism H i)) ≈S
    v (d[Z; 2; fin_first] (two_sphere_prism H i)) ⋅
      v (d[Z; 2; fin_first⁺⁺] (two_sphere_prism H i))).
  { intros i. exact (cocycle_tetrahedron_face_equation (two_sphere_prism H i)). }
  pose proof (E fin_first) as E0.
  pose proof (E fin_first⁺) as E1.
  pose proof (E fin_first⁺⁺) as E2.
  rewrite (two_sphere_prism_faces H fin_first fin_first⁺⁺⁺),
    (two_sphere_prism_faces H fin_first fin_first⁺),
    (two_sphere_prism_faces H fin_first fin_first),
    (two_sphere_prism_faces H fin_first fin_first⁺⁺) in E0.
  rewrite (two_sphere_prism_faces H fin_first⁺ fin_first⁺⁺⁺),
    (two_sphere_prism_faces H fin_first⁺ fin_first⁺),
    (two_sphere_prism_faces H fin_first⁺ fin_first),
    (two_sphere_prism_faces H fin_first⁺ fin_first⁺⁺) in E1.
  rewrite (two_sphere_prism_faces H fin_first⁺⁺ fin_first⁺⁺⁺),
    (two_sphere_prism_faces H fin_first⁺⁺ fin_first⁺),
    (two_sphere_prism_faces H fin_first⁺⁺ fin_first),
    (two_sphere_prism_faces H fin_first⁺⁺ fin_first⁺⁺) in E2.
  change ((1 : M) ⋅ v b ≈S v y.1 ⋅ 1) in E0.
  change ((1 : M) ⋅ v b ≈S 1 ⋅ v a) in E1.
  change (v x.1 ⋅ 1 ≈S 1 ⋅ v a) in E2.
  rewrite monoid_unit_l, monoid_unit_r in E0, E2.
  rewrite !monoid_unit_l in E1.
  change (v x.1 ≈S v y.1).
  transitivity (v a); [exact E2 |].
  transitivity (v b); [symmetry; exact E1 | exact E0].
Defined.

(** The whole relative cylinder induces the existing generated class
    equality, by the coefficient classifier. *)

(** 完整相对柱经系数分类诱导既有生成类相等。 *)

Definition cocycle_two_sphere_cylinder_class (x y : Q)
    (H : TwoSphereCylinderHomotopy Z (two_cocycle_simplex_unit 0) x y)
  : x ≈S y.
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  exact (cocycle_two_sphere_cylinder_value x y H).
Defined.

(** Equal generated classes construct a genuine time-independent cylinder.
    This uses the special triangle classification of the cocycle model;
    no such native-triangle reflection is assumed for other simplicial sets. *)

(** 相等生成类构造真实的时间无关柱。此处使用 cocycle 模型特有的三角形分类；
    不对其他单纯集合预设这类原生三角形相等反映性。 *)

Definition CocycleTwoSphereCylinder (x y : Q) (H : x ≈S y)
  : TwoSphereCylinderHomotopy Z (two_cocycle_simplex_unit 0) x y.
Proof.
  apply TwoSphereConstantCylinder.
  change (x.1 ≈S y.1). apply cocycle_triangle_eq_of_value.
  exact (@func_proper _ _ cocycle_two_sphere_class_value_resp _ _ H).
Defined.

(** Two transparent transformations identify the cylinder presentation
    with generated tetrahedron class equality, without identifying their
    witness types or the stored homotopies themselves. *)

(** 两个透明转换将柱呈现与生成四面体类相等联系起来，不识别二者的见证类型，
    也不比较所保存同伦本身。 *)

Definition cocycle_two_sphere_cylinder_iff (x y : Q)
  : TwoSphereCylinderHomotopy Z (two_cocycle_simplex_unit 0) x y ↔ x ≈S y
  := (cocycle_two_sphere_cylinder_class x y, CocycleTwoSphereCylinder x y).

(** In this model the directed relative-cylinder relation is already an
    equivalence. Its witnesses for reversal and concatenation are obtained
    through classification, not by assuming an interval reversal map. *)

(** 在此模型中，有向相对柱关系本身已为等价关系。反向与拼接见证经分类得到，
    不预设区间的反向映射。 *)

Global Instance cocycle_two_sphere_cylinder_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z (two_cocycle_simplex_unit 0)).
Proof.
  split.
  - intros x. exact (CocycleTwoSphereCylinder x x (reflexivity (x : Q))).
  - intros x y H. apply CocycleTwoSphereCylinder.
    symmetry. exact (cocycle_two_sphere_cylinder_class x y H).
  - intros x y z H K. apply CocycleTwoSphereCylinder.
    transitivity (y : Q).
    + exact (cocycle_two_sphere_cylinder_class x y H).
    + exact (cocycle_two_sphere_cylinder_class y z K).
Defined.

End CocycleCylinderComparison.
