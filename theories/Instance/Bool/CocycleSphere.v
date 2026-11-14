From Cats Require Export
  Instance.Bool.CocycleKan
  Instance.Set.Simplicial.Cocycle.Sphere.
From Cats Require
  Instance.Set.Simplicial.Vertex.Sphere.

Import Cats.Instance.Set.Groupoid (EqGpd).
Import Cats.Instance.Set.Simplicial.Vertex.Core (VertexNerve).
Import Cats.Instance.Set.Simplicial.Vertex.Sphere (vertex_two_sphere_unique).

Local Existing Instance BoolS_Monoid.

(** * Two Sphere Classes in an Actual Kan Model

    The Boolean model already has full selected Kan fillers. The new
    coefficient invariant now shows that the true-labelled sphere cannot
    be related to the constant sphere by any finite chain of elementary
    based tetrahedron homotopies, reversals or specified equalities.

    Ordinary category nerves have only one based two-sphere, by
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Sphere.vertex two sphere unique}
    {%[vertex_two_sphere_unique]%}%. Naturality and component inverses
    therefore exclude a natural isomorphism from the Boolean cocycle model
    to any such nerve, including groupoid nerves. This is a proved
    combinatorial distinction. The next chapter
    %\coqref{Cats.Instance.Bool.CocycleSphereGroup.BoolCocycleSphereClassS Group}
    {%[BoolCocycleSphereClassS_Group]%}% supplies an order-two group on these
    classes. Identification with other homotopy presentations and their
    invariance remain further work. *)

(** * 实际 Kan 模型中的两个球面类

    布尔模型已具备完整选定 Kan 填充。新的系数不变量进一步证明：标签为真
    的球面，不能经任意有限次基点四面体初等同伦、反向及指定相等，联系到
    常值球面。

    由 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Sphere.vertex two sphere unique}
    {%[vertex_two_sphere_unique]%}%，普通范畴 nerve 只有一个基点二维球面。
    自然性及分量的逆因此排除布尔 cocycle 模型与任意此类 nerve 的自然同构，
    其中包括群胚 nerve。这是已证明的组合区别。下一章
    %\coqref{Cats.Instance.Bool.CocycleSphereGroup.BoolCocycleSphereClassS Group}
    {%[BoolCocycleSphereClassS_Group]%}% 为这些类构造二阶群；与其他同伦呈现
    的识别及其不变性仍须后续工作。 *)

(** The actual sphere-class setoid at the unit vertex. *)

(** 单位顶点处的实际球面类广集。 *)

Definition BoolCocycleSphereClassS
  : SetC
  := TwoSphereClassS BoolCocycleModel (two_cocycle_simplex_unit 0).

(** The true coefficient gives a specified based sphere. *)

(** 真系数给出一份指定基点球面。 *)

Definition bool_cocycle_sphere
  : BoolCocycleSphereClassS
  := cocycle_two_sphere_resp true.

(** This sphere is not null under the entire generated relation. *)

(** 此球面在整个生成关系下仍不为零。 *)

Lemma bool_cocycle_sphere_not_null
  : ¬ (bool_cocycle_sphere ≈S
      two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)).
Proof.
  intros H.
  pose proof (@func_proper _ _ cocycle_two_sphere_class_value_resp _ _ H) as E.
  change (true = false) in E. discriminate E.
Defined.

(** ** Comparison at Independent Ambient Sizes

    Fix any ordinary category and its object presentation. Both nerves
    and the Boolean cocycle model are raised to common ambient bounds;
    no restriction identifies the category's native hom sizes. *)

(** ** 独立环境大小中的比较

    固定任意普通范畴及其对象呈现。将 nerve 与布尔 cocycle 模型提升至共同
    环境界，不要求识别范畴原生 Hom 大小。 *)

Section NerveComparison.
Universes u p.
Context {A : SetC} {C : Cat} (T : Fct (EqGpd A) C).

(** No natural isomorphism identifies this model with an ordinary nerve.
    The proof maps two spheres forward and reflects their forced equality
    through the inverse of the degree-two component. *)

(** 不存在将此模型识别为普通 nerve 的自然同构。证明先映射两个球面，再由
    二维分量的逆反映其被迫成立的相等。 *)

Lemma bool_cocycle_not_vertex_nerve
  : ¬ ((Z²(BoolS) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      (VertexNerve T : Fct (Δ^op) SetCat@{u p _ _ _ _ _})).
Proof.
  intros [α Hα].
  pose (B := (Z²(BoolS) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})).
  pose (b := (two_cocycle_simplex_unit 0 : B 0)).
  pose (f := (cocycle_two_sphere_resp : BoolS →r TwoSphereS B b)).
  pose (x := f true). pose (y := f false).
  pose proof (vertex_two_sphere_unique T (α 0 b)
    (two_sphere_map_resp α b x) (two_sphere_map_resp α b y)) as E.
  assert (Q : x.1 ≈S y.1).
  { transitivity ((Hα 2).1 (α 2 x.1)).
    - symmetry. exact (fst (Hα 2).2 x.1).
    - transitivity ((Hα 2).1 (α 2 y.1)).
      + exact (@func_proper _ _ (Hα 2).1 _ _ E).
      + exact (fst (Hα 2).2 y.1). }
  pose proof (@func_proper _ _ two_cocycle_triangle_value_resp _ _ Q) as K.
  change (true = false) in K. discriminate K.
Defined.

End NerveComparison.
