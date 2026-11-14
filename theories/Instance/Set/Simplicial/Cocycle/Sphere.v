From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Finite
  Instance.Set.Simplicial.Homotopy.Sphere.
From Cats Require Import
  Instance.Set.Isomorphism.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope monoid_scope.

(** * Coefficients Classify Based Two-Spheres

    The low-degree decoder
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Low.two cocycle triangle value resp}
    {%[two_cocycle_triangle_value_resp]%}% gives every triangle a coefficient.
    Distinct
    coefficients alone were not yet a homotopy argument. Now an actual
    tetrahedron with its first two faces constant forces its remaining
    two coefficients to agree: its cocycle equation reduces to
    [b ⋅ 1 ≈S 1 ⋅ a]. Conversely, equal coefficients give such a tetrahedron.
    The coefficient therefore classifies the generated sphere relation,
    including arbitrary finite chains and changes of representative.

    Only a monoid is needed for this calculation. The separately proved
    Kan theorem needs commutative group coefficients. This chapter computes
    a sphere-class setoid. The next chapter
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.SphereGroup.cocycle two sphere Group}
    {%[cocycle_two_sphere_Group]%}% equips it with a group operation witnessed
    by tetrahedra; comparison with cylinder presentations remains separate. *)

(** * 系数分类基点二维球面

    低维读取映射
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Low.two cocycle triangle value resp}
    {%[two_cocycle_triangle_value_resp]%}% 为每个三角形给出系数，但不同系数本身尚非
    同伦论证。现在，若
    实际四面体的前两个面为常值，则 cocycle 方程简化为 [b ⋅ 1 ≈S 1 ⋅ a]，
    从而迫使余下两个面的系数相等。反之，相等系数给出这样的四面体。因此，
    系数分类整个生成球面关系，包括任意有限链与代表替换。

    这个计算只需幺半群；独立证明的 Kan 定理要求交换群系数。本章计算球面类
    广集。下一章
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.SphereGroup.cocycle two sphere Group}
    {%[cocycle_two_sphere_Group]%}% 赋予它具有四面体见证的群运算；柱呈现比较
    仍是独立任务。 *)

(** ** Spheres in the Cocycle Model

    Fix a coefficient monoid and independent ambient sizes. The basepoint
    is the unit vertex. Every triangle has the required constant boundary
    because degree one is unique in specified equality. *)

(** ** Cocycle 模型中的球面

    固定系数幺半群及独立环境大小，以单位顶点为基点。一维在指定相等下唯一，
    因此每个三角形都具有所需的常值边界。 *)

Section CocycleSpheres.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}.

Let Z
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

(** Regard a freely labelled triangle as a based sphere. *)

(** 将自由标记的三角形视作基点球面。 *)

Program Definition cocycle_two_sphere_resp
  : M →r TwoSphereS Z (two_cocycle_simplex_unit 0)
  :=
  {|func a := (two_cocycle_triangle_resp a; _)
  |}.
Next Obligation.
  intros i. exact (@two_cocycle_one_unique M HM
    (d[Z; 1; i] (two_cocycle_triangle_resp a))
    (simplex_constant Z (two_cocycle_simplex_unit 0) 1)).
Defined.
Next Obligation.
  intros a b H. exact (@func_proper _ _ two_cocycle_triangle_resp a b H).
Defined.

(** Decode the underlying triangle, ignoring boundary witnesses. *)

(** 读取底层三角形，不比较边界见证。 *)

Program Definition cocycle_two_sphere_value_resp
  : TwoSphereS Z (two_cocycle_simplex_unit 0) →r M
  :=
  {|func x := two_cocycle_triangle_value_resp x.1
  |}.
Next Obligation.
  intros x y H. exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _ H).
Defined.

(** The four oriented face coefficients satisfy the tetrahedron equation. *)

(** 四个定向面系数满足四面体方程。 *)

Lemma cocycle_tetrahedron_face_equation (w : Z 3)
  : two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺⁺⁺] w) ⋅
      two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺] w) ≈S
    two_cocycle_triangle_value_resp (d[Z; 2; fin_first] w) ⋅
      two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺⁺] w).
Proof.
  pose (f := ordinal_step (@fin_first 2)).
  pose (g := ordinal_step (fin_next (@fin_first 1))).
  pose (h := ordinal_step (fin_next (fin_next (@fin_first 0)))).
  pose (a := ordinal_step (@fin_first 1)).
  pose (b := ordinal_step (fin_next (@fin_first 0))).
  change ((lower w)⟦fmap δ[2; fin_first⁺⁺⁺] a,
      fmap δ[2; fin_first⁺⁺⁺] b⟧₂ ⋅
    (lower w)⟦fmap δ[2; fin_first⁺] a, fmap δ[2; fin_first⁺] b⟧₂ ≈S
    (lower w)⟦fmap δ[2; fin_first] a, fmap δ[2; fin_first] b⟧₂ ⋅
    (lower w)⟦fmap δ[2; fin_first⁺⁺] a, fmap δ[2; fin_first⁺⁺] b⟧₂).
  transitivity ((lower w)⟦f, g⟧₂ ⋅ (lower w)⟦g ∘ f, h⟧₂).
  - apply magma_mul_proper; apply ordinal_cocycle_triangle_transport;
      reflexivity.
  - transitivity ((lower w)⟦g, h⟧₂ ⋅ (lower w)⟦f, h ∘ g⟧₂).
    + apply two_cocycle_tetrahedron.
    + apply magma_mul_proper; apply ordinal_cocycle_triangle_transport;
        reflexivity.
Defined.

(** A constant triangle has unit coefficient. *)

(** 常值三角形的系数为单位。 *)

Lemma cocycle_constant_triangle_value
  : two_cocycle_triangle_value_resp
      (simplex_constant Z (two_cocycle_simplex_unit 0) 2) ≈S 1.
Proof. reflexivity. Defined.

(** Every actual elementary based homotopy preserves the coefficient. *)

(** 每份实际基点初等同伦均保持系数。 *)

Lemma cocycle_two_sphere_homotopy_value
    (x y : TwoSphereS Z (two_cocycle_simplex_unit 0))
    (H : TwoSphereHomotopy Z (two_cocycle_simplex_unit 0) x y)
  : cocycle_two_sphere_value_resp x ≈S cocycle_two_sphere_value_resp y.
Proof.
  change (two_cocycle_triangle_value_resp x.1 ≈S
    two_cocycle_triangle_value_resp y.1).
  destruct H as [w [H0 [H1 [H2 H3]]]].
  pose proof (cocycle_tetrahedron_face_equation w) as E.
  assert (V0 : two_cocycle_triangle_value_resp
      (d[Z; 2; fin_first] w) ≈S 1).
  { transitivity (two_cocycle_triangle_value_resp
      (simplex_constant Z (two_cocycle_simplex_unit 0) 2)).
    - apply func_proper. exact H0.
    - apply cocycle_constant_triangle_value. }
  assert (V1 : two_cocycle_triangle_value_resp
      (d[Z; 2; fin_first⁺] w) ≈S 1).
  { transitivity (two_cocycle_triangle_value_resp
      (simplex_constant Z (two_cocycle_simplex_unit 0) 2)).
    - apply func_proper. exact H1.
    - apply cocycle_constant_triangle_value. }
  rewrite V0, V1, monoid_unit_l, monoid_unit_r in E.
  transitivity (two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺⁺] w)).
  - symmetry. apply func_proper. exact H2.
  - transitivity (two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺⁺⁺] w)).
    + symmetry. exact E.
    + apply func_proper. exact H3.
Defined.

(** Equal coefficients give an actual tetrahedron, with unit first faces
    and the specified endpoints as its last two faces. *)

(** 相等系数给出实际四面体，前两面为单位，后两面为指定端点。 *)

Definition CocycleTwoSphereHomotopy
    (x y : TwoSphereS Z (two_cocycle_simplex_unit 0))
    (H : cocycle_two_sphere_value_resp x ≈S cocycle_two_sphere_value_resp y)
  : TwoSphereHomotopy Z (two_cocycle_simplex_unit 0) x y.
Proof.
  assert (E : cocycle_two_sphere_value_resp y ⋅ 1 ≈S
      1 ⋅ cocycle_two_sphere_value_resp x).
  { rewrite monoid_unit_l, monoid_unit_r. symmetry. exact H. }
  exists {|lower := TetrahedronTwoCocycle
    (cocycle_two_sphere_value_resp y) 1 1 (cocycle_two_sphere_value_resp x) E
    |}.
  split; [| split; [| split]];
    apply cocycle_triangle_eq_of_value.
  - symmetry. apply cocycle_constant_triangle_value.
  - symmetry. apply cocycle_constant_triangle_value.
  - reflexivity.
  - reflexivity.
Defined.

(** The actual elementary relation itself is exactly coefficient equality;
    the generated closure introduces no additional identifications. *)

(** 实际初等关系本身就恰为系数相等；生成闭包不会引入更多识别。 *)

Definition cocycle_two_sphere_homotopy_iff
    (x y : TwoSphereS Z (two_cocycle_simplex_unit 0))
  : TwoSphereHomotopy Z (two_cocycle_simplex_unit 0) x y ↔
      cocycle_two_sphere_value_resp x ≈S cocycle_two_sphere_value_resp y
  := (cocycle_two_sphere_homotopy_value x y, CocycleTwoSphereHomotopy x y).

(** The coefficient is an invariant of the whole generated relation,
    obtained by the general descent theorem rather than a second induction. *)

(** 由一般下降定理，系数成为整个生成关系的不变量，无须另写一份归纳证明。 *)

Definition cocycle_two_sphere_class_value_resp
  : TwoSphereClassS Z (two_cocycle_simplex_unit 0) →r M
  := two_sphere_class_desc Z (two_cocycle_simplex_unit 0)
      cocycle_two_sphere_value_resp cocycle_two_sphere_homotopy_value.

(** Class equality is exactly coefficient equality. Both directions
    transform retained witnesses; they do not identify witness types. *)

(** 类相等恰为系数相等。两个方向转换保留见证，不识别见证类型。 *)

Definition cocycle_two_sphere_class_eq_iff
    (x y : TwoSphereClassS Z (two_cocycle_simplex_unit 0))
  : x ≈S y ↔
      cocycle_two_sphere_class_value_resp x ≈S
        cocycle_two_sphere_class_value_resp y.
Proof.
  split.
  - apply func_proper.
  - intros H. apply two_sphere_class_step.
    exact (CocycleTwoSphereHomotopy x y H).
Defined.

(** Construct a sphere class from its coefficient, respecting coefficient
    equality through the original triangle equality. *)

(** 由系数构造球面类，经原三角形相等保持系数相等。 *)

Program Definition cocycle_two_sphere_class_resp
  : M →r TwoSphereClassS Z (two_cocycle_simplex_unit 0)
  :=
  {|func a := cocycle_two_sphere_resp a
  |}.
Next Obligation.
  intros a b H.
  exact (two_sphere_class_eq Z (two_cocycle_simplex_unit 0)
    (@func_proper _ _ cocycle_two_sphere_resp a b H)).
Defined.

(** Evaluation after class construction recovers the coefficient. *)

(** 先构造类再求值，恢复系数。 *)

Lemma cocycle_two_sphere_class_β (a : M)
  : cocycle_two_sphere_class_value_resp (cocycle_two_sphere_class_resp a) ≈S a.
Proof. apply two_cocycle_triangle_β. Defined.

(** Construction after evaluation recovers the original sphere class. *)

(** 先求值再构造，恢复原球面类。 *)

Lemma cocycle_two_sphere_class_η
    (x : TwoSphereClassS Z (two_cocycle_simplex_unit 0))
  : cocycle_two_sphere_class_resp (cocycle_two_sphere_class_value_resp x) ≈S x.
Proof. apply two_sphere_class_eq. apply two_cocycle_triangle_η. Defined.

(** Common upward lifts package the two respectful maps as an actual
    setoid isomorphism. No arbitrary resizing of class witnesses is used.
    Here q is the class projection; the triangle commutes because the
    descended evaluation reads the same retained representative. Its inverse
    sends a coefficient to the class of its freely labelled triangle. *)

(** 共同向上提升将两个保相等映射打包为实际广集同构，不任意重设类见证大小。
    图中 q 是类投影；下降后的求值读取同一个保留代表，因此三角形交换。
    逆映射将系数送到相应自由标记三角形的类。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
\operatorname{Sphere}_2(Z^2(M),\ast)
  \arrow[r,"{c_{012}}"] \arrow[d,"q"'] & M \\
\operatorname{SphereClass}_2(Z^2(M),\ast)
  \arrow[ur,"{\overline{c}_{012}}"',"\cong"] &
\end{tikzcd}
\end{center}%
*)

Definition cocycle_two_sphere_class_iso@{v q +}
  : LiftS@{_ _ v q} (TwoSphereClassS Z (two_cocycle_simplex_unit 0))
      ≅[SetCat@{v q _ _ _ _ _}] LiftS@{_ _ v q} M.
Proof.
  exists (cocycle_two_sphere_class_value_resp^↑S),
    (cocycle_two_sphere_class_resp^↑S). split.
  - intros [x]. exact {|lower := cocycle_two_sphere_class_η x
                       |}.
  - intros [a]. exact {|lower := cocycle_two_sphere_class_β a
                       |}.
Defined.

End CocycleSpheres.
