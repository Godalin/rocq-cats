From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Sphere
  Instance.Set.Simplicial.Homotopy.SphereComposition
  Algebra.Group.Core
  Algebra.Monoid.Commutative.
From Cats Require Import
  Instance.Set.Simplicial.Matching.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope monoid_scope.

(** * Multiplication of Cocycle Sphere Classes

    The coefficient classification from
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Sphere.cocycle two sphere class eq iff}
    {%[cocycle_two_sphere_class_eq_iff]%}% lets us define a respectful class
    product. Its geometric meaning comes from an actual tetrahedron:
    [d_3 w=x], [d_1 w=y], [d_0 w=base] imply [cx ⋅ cy ≈S cz] for
    [z=d_2 w]. Conversely every such equation constructs a tetrahedron.
    Therefore every filler with these faces gives the chosen product class.

    Monoid coefficients suffice for this composition calculation. Group
    coefficients give inverses; commutative coefficients give a commutative
    class operation. For an abelian group the previously constructed Kan
    model thus has a group on this simplex presentation of sphere classes.
    Comparison with cylinder homotopy and homotopy-equivalence invariance
    remain separate tasks; we do not use this result to exclude all 1-types. *)

(** * Cocycle 球面类的乘法

    前章的系数分类
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Sphere.cocycle two sphere class eq iff}
    {%[cocycle_two_sphere_class_eq_iff]%}% 允许定义保相等的类乘法。其几何意义
    来自实际四面体：[d_3 w=x]、[d_1 w=y]、[d_0 w=base] 使 [z=d_2 w]
    满足 [cx ⋅ cy ≈S cz]。反之，每份这样的方程都构造一个四面体。
    因而具有这些面的任意填充都给出选定乘积类。

    此合成计算只需幺半群系数；群系数给出逆，交换系数给出类运算的交换律。
    因此，对交换群系数，先前构造的 Kan 模型在这一单形球面类呈现上具备群。
    与柱同伦的比较、同伦等价不变性仍是独立任务；不据此排除所有 1-types。 *)

(** ** A Monoid on the Classified Spheres

    Fix a coefficient monoid and independent ambient simplex sizes.
    Multiplication uses the two respectful classification maps; equality
    remains the generated tetrahedron relation, not equality of functions
    or boundary witnesses. The unit is the actual constant sphere. *)

(** ** 已分类球面上的幺半群

    固定系数幺半群及独立环境单形大小。乘法使用分类的两个保相等映射；
    相等仍为生成四面体关系，不是函数或边界见证的相等。单位为实际常值球面。 *)

Section SphereMonoid.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}.

Let Z
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

Let Q
  : SetC
  := TwoSphereClassS Z (two_cocycle_simplex_unit 0).

(** Encode the product of the two decoded coefficients. *)

(** 编码读取出的两个系数的乘积。 *)

Definition cocycle_two_sphere_mul (x y : Q)
  : Q
  := cocycle_two_sphere_class_resp
      (cocycle_two_sphere_class_value_resp x ⋅
        cocycle_two_sphere_class_value_resp y).

(** Evaluation preserves the chosen multiplication. *)

(** 求值保持选定乘法。 *)

Lemma cocycle_two_sphere_mul_value (x y : Q)
  : cocycle_two_sphere_class_value_resp (cocycle_two_sphere_mul x y) ≈S
      cocycle_two_sphere_class_value_resp x ⋅
        cocycle_two_sphere_class_value_resp y.
Proof. apply cocycle_two_sphere_class_β. Defined.

(** The product respects the entire generated relation in both inputs. *)

(** 乘积在两个输入处均保持整个生成关系。 *)

Global Instance cocycle_two_sphere_mul_proper
  : Proper ([≈S] ==> [≈S] ==> [≈S]) cocycle_two_sphere_mul.
Proof.
  intros x x' E y y' F. apply func_proper. apply magma_mul_proper;
    apply func_proper; assumption.
Defined.

(** Select only the multiplication, without registering a model instance. *)

(** 只选择乘法，不注册模型实例。 *)

Program Definition cocycle_two_sphere_Magma
  : Magma Q
  :=
  {|magma_mul := cocycle_two_sphere_mul
  |}.

(** Associativity follows by decoding, using the coefficient law. *)

(** 结合律经读取后由系数的定律得到。 *)

Lemma cocycle_two_sphere_mul_assoc (x y z : Q)
  : cocycle_two_sphere_mul (cocycle_two_sphere_mul x y) z ≈S
      cocycle_two_sphere_mul x (cocycle_two_sphere_mul y z).
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  repeat rewrite cocycle_two_sphere_mul_value.
  apply semigroup_assoc.
Defined.

(** Keep exactly the selected magma as the semigroup's parent. *)

(** 半群只以选定原群为父结构。 *)

Program Definition cocycle_two_sphere_Semigroup
  : Semigroup Q
  :=
  {|SemigroupM := cocycle_two_sphere_Magma
  ; semigroup_assoc := cocycle_two_sphere_mul_assoc
  |}.

(** The constant sphere is a left unit in generated class equality. *)

(** 常值球面在生成类相等下为左单位。 *)

Lemma cocycle_two_sphere_unit_l (x : Q)
  : cocycle_two_sphere_mul (two_sphere_base Z (two_cocycle_simplex_unit 0)) x
      ≈S x.
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_mul_value.
  change (two_cocycle_triangle_value_resp
    (simplex_constant Z (two_cocycle_simplex_unit 0) 2) ⋅
    cocycle_two_sphere_class_value_resp x ≈S
    cocycle_two_sphere_class_value_resp x).
  change ((1 : M) ⋅ cocycle_two_sphere_class_value_resp x ≈S
    cocycle_two_sphere_class_value_resp x).
  apply monoid_unit_l.
Defined.

(** The same constant sphere is a right unit. *)

(** 同一个常值球面也是右单位。 *)

Lemma cocycle_two_sphere_unit_r (x : Q)
  : cocycle_two_sphere_mul x (two_sphere_base Z (two_cocycle_simplex_unit 0))
      ≈S x.
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_mul_value.
  change (cocycle_two_sphere_class_value_resp x ⋅
    two_cocycle_triangle_value_resp
      (simplex_constant Z (two_cocycle_simplex_unit 0) 2) ≈S
    cocycle_two_sphere_class_value_resp x).
  change (cocycle_two_sphere_class_value_resp x ⋅ (1 : M) ≈S
    cocycle_two_sphere_class_value_resp x).
  apply monoid_unit_r.
Defined.

(** A chosen monoid with the actual base sphere as its unit. *)

(** 以实际基点球面为单位的选定幺半群。 *)

Program Definition cocycle_two_sphere_Monoid
  : Monoid Q
  :=
  {|MonoidSG := cocycle_two_sphere_Semigroup
  ; monoid_unit := two_sphere_base Z (two_cocycle_simplex_unit 0)
  ; monoid_unit_l := cocycle_two_sphere_unit_l
  ; monoid_unit_r := cocycle_two_sphere_unit_r
  |}.

(** ** Actual Fillers and Independence of Their Choice

    The orientation of the four faces is essential: the existing
    tetrahedron equation reads [c3 ⋅ c1 ≈S c0 ⋅ c2]. With [c0=1]
    it is precisely the product equation. Both directions below are
    transparent witness transformations, without equality of law records. *)

(** ** 实际填充及其选择无关性

    四个面的定向至关重要：既有四面体方程是 [c3 ⋅ c1 ≈S c0 ⋅ c2]。
    当 [c0=1] 时它恰为乘积方程。下面两个方向均为透明见证转换，不要求定律
    记录相等。 *)

(** Every actual composite has the product coefficient. *)

(** 每份实际合成都具有乘积系数。 *)

Lemma cocycle_two_sphere_composite_value
    (x y z : TwoSphereS Z (two_cocycle_simplex_unit 0))
    (H : TwoSphereComposite Z (two_cocycle_simplex_unit 0) x y z)
  : cocycle_two_sphere_value_resp x ⋅ cocycle_two_sphere_value_resp y ≈S
      cocycle_two_sphere_value_resp z.
Proof.
  change (two_cocycle_triangle_value_resp x.1 ⋅
    two_cocycle_triangle_value_resp y.1 ≈S
    two_cocycle_triangle_value_resp z.1).
  destruct H as [w [H0 [H1 [H2 H3]]]].
  pose proof (cocycle_tetrahedron_face_equation w) as E.
  assert (V0 : two_cocycle_triangle_value_resp
      (d[Z; 2; fin_first] w) ≈S 1).
  { transitivity (two_cocycle_triangle_value_resp
      (simplex_constant Z (two_cocycle_simplex_unit 0) 2)).
    - apply func_proper. exact H0.
    - apply cocycle_constant_triangle_value. }
  change (two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺⁺⁺] w) ⋅
    two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺] w) ≈S
    two_cocycle_triangle_value_resp (d[Z; 2; fin_first] w) ⋅
    two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺⁺] w)) in E.
  rewrite V0, monoid_unit_l in E.
  transitivity (two_cocycle_triangle_value_resp
      (d[Z; 2; fin_first⁺⁺⁺] w) ⋅
    two_cocycle_triangle_value_resp (d[Z; 2; fin_first⁺] w)).
  - apply magma_mul_proper; symmetry; apply func_proper; assumption.
  - transitivity (two_cocycle_triangle_value_resp
      (d[Z; 2; fin_first⁺⁺] w)); [exact E |].
    apply func_proper. exact H2.
Defined.

(** A product equation builds a real tetrahedron, with all faces specified. *)

(** 乘积方程构造真实四面体，并指定全部面。 *)

Definition CocycleTwoSphereComposite
    (x y z : TwoSphereS Z (two_cocycle_simplex_unit 0))
    (H : cocycle_two_sphere_value_resp x ⋅ cocycle_two_sphere_value_resp y
      ≈S cocycle_two_sphere_value_resp z)
  : TwoSphereComposite Z (two_cocycle_simplex_unit 0) x y z.
Proof.
  assert (E : cocycle_two_sphere_value_resp x ⋅
      cocycle_two_sphere_value_resp y ≈S
      1 ⋅ cocycle_two_sphere_value_resp z).
  { rewrite monoid_unit_l. exact H. }
  exists {|lower := TetrahedronTwoCocycle
    (cocycle_two_sphere_value_resp x) (cocycle_two_sphere_value_resp y)
    1 (cocycle_two_sphere_value_resp z) E
    |}.
  split; [| split; [| split]]; apply cocycle_triangle_eq_of_value.
  - symmetry. apply cocycle_constant_triangle_value.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(** The geometric relation is exactly the product equation. *)

(** 几何关系恰为乘积方程。 *)

Definition cocycle_two_sphere_composite_iff
    (x y z : TwoSphereS Z (two_cocycle_simplex_unit 0))
  : TwoSphereComposite Z (two_cocycle_simplex_unit 0) x y z ↔
      cocycle_two_sphere_value_resp x ⋅ cocycle_two_sphere_value_resp y ≈S
        cocycle_two_sphere_value_resp z
  := (cocycle_two_sphere_composite_value x y z,
      CocycleTwoSphereComposite x y z).

(** The chosen product is itself witnessed by an actual tetrahedron. *)

(** 选定乘积本身有实际四面体见证。 *)

Definition CocycleTwoSphereMul (x y : Q)
  : TwoSphereComposite Z (two_cocycle_simplex_unit 0)
      x y (cocycle_two_sphere_mul x y).
Proof.
  apply CocycleTwoSphereComposite.
  symmetry. apply cocycle_two_sphere_mul_value.
Defined.

(** Any other actual composite gives the same generated class. *)

(** 任何其他实际合成都给出相同生成类。 *)

Lemma cocycle_two_sphere_composite_unique (x y z : Q)
    (H : TwoSphereComposite Z (two_cocycle_simplex_unit 0) x y z)
  : z ≈S cocycle_two_sphere_mul x y.
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  transitivity (cocycle_two_sphere_class_value_resp x ⋅
      cocycle_two_sphere_class_value_resp y).
  - symmetry. exact (cocycle_two_sphere_composite_value x y z H).
  - symmetry. apply cocycle_two_sphere_mul_value.
Defined.

(** The actual horn retains faces zero, one and three of our tetrahedron.
    Restriction omits face two itself, while retaining its boundary through
    the other faces. It is a map from the existing horn presheaf. *)

(** 实际角保留所构造四面体的第零、第一及第三面。限制略去第二面本身，仍经
    其他面保留其边界。这是从既有 horn 预层出发的映射。 *)

Definition cocycle_two_sphere_horn (x y : Q)
  : HornS Z 3 fin_first⁺⁺
  := (CocycleTwoSphereMul x y).1↾Λ[Z; 3; fin_first⁺⁺].

(** Every tetrahedron's second face is a sphere in this model, since
    all its edges agree with the unique constant edge. *)

(** 此模型中每个四面体的第二面都是球面，因为其全部边均等于唯一常值边。 *)

Program Definition cocycle_two_sphere_face (w : Z 3)
  : TwoSphereS Z (two_cocycle_simplex_unit 0)
  := (d[Z; 2; fin_first⁺⁺] w; _).
Next Obligation.
  intros i. exact (@two_cocycle_one_unique M HM
    (d[Z; 1; i] (d[Z; 2; fin_first⁺⁺] w))
    (simplex_constant Z (two_cocycle_simplex_unit 0) 1)).
Defined.

(** Any filler of the actual horn supplies a composite witness. This
    applies in particular to the previously chosen Kan filler, but does
    not rely on that choice or require extra coefficient hypotheses. *)

(** 实际角的任意填充均提供合成见证。此结论尤其适用于先前的选定 Kan 填充，
    但不依赖该选择，也不要求额外系数假设。 *)

Definition CocycleTwoSphereHornComposite (x y : Q) (w : Z 3)
    (H : is_horn_filler (cocycle_two_sphere_horn x y) w)
  : TwoSphereComposite Z (two_cocycle_simplex_unit 0)
      x y (cocycle_two_sphere_face w).
Proof.
  pose (t := CocycleTwoSphereMul x y).
  assert (F : ∀ j : Ordinal 3, ¬ j = fin_first⁺⁺ →
      d[Z; 2; j] w ≈S d[Z; 2; j] t.1).
  { intros j E. exact (fst (horn_filler_faces_iff
      (cocycle_two_sphere_horn x y) w) H j E). }
  exists w. split; [| split; [| split]].
  - transitivity (d[Z; 2; fin_first] t.1).
    + apply F. discriminate.
    + exact (fst t.2).
  - transitivity (d[Z; 2; fin_first⁺] t.1).
    + apply F. discriminate.
    + exact (fst (snd t.2)).
  - reflexivity.
  - transitivity (d[Z; 2; fin_first⁺⁺⁺] t.1).
    + apply F. discriminate.
    + exact (snd (snd (snd t.2))).
Defined.

(** The missing face of every actual horn filler is the same product
    class, not necessarily the same native triangle or filler record. *)

(** 每份实际角填充的缺面都属于同一乘积类，不要求原生三角形或填充记录相等。 *)

Lemma cocycle_two_sphere_horn_unique (x y : Q) (w : Z 3)
    (H : is_horn_filler (cocycle_two_sphere_horn x y) w)
  : (cocycle_two_sphere_face w : Q) ≈S cocycle_two_sphere_mul x y.
Proof.
  exact (cocycle_two_sphere_composite_unique x y _
    (CocycleTwoSphereHornComposite x y w H)).
Defined.

(** Let [Q] denote this sphere-class setoid and [v] its descended
    coefficient map. The square commutes in specified coefficient equality
    by [cocycle_two_sphere_mul_value]. Its vertical maps are the coefficient
    classification; their respectful inverses also preserve products and
    units by the following laws. The product symbols in this diagram
    describe pairs of elements, without selecting categorical products. *)

(** 以 [Q] 表示此球面类广集，[v] 表示下降后的系数映射。由
    [cocycle_two_sphere_mul_value]，方图按指定系数相等交换。竖直映射是系数
    分类；接下来的定律说明其保相等逆也保持乘积和单位。图中的乘积符号表示
    元素对，不涉及选定范畴积。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
Q\times Q \arrow[r,"{\mu}"] \arrow[d,"{v\times v}"']
  & Q \arrow[d,"v"] \\
M\times M \arrow[r,"{\cdot}"'] & M
\end{tikzcd}
\end{center}%
*)

(** Encoding coefficients preserves their product, in class equality. *)

(** 编码系数在类相等下保持其乘积。 *)

Lemma cocycle_two_sphere_class_mul (a b : M)
  : cocycle_two_sphere_class_resp (a ⋅ b) ≈S
      cocycle_two_sphere_mul (cocycle_two_sphere_class_resp a)
        (cocycle_two_sphere_class_resp b).
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_mul_value.
  repeat rewrite cocycle_two_sphere_class_β. reflexivity.
Defined.

(** Encoding the coefficient unit gives the actual constant sphere class. *)

(** 编码系数单位给出实际常值球面类。 *)

Lemma cocycle_two_sphere_class_unit
  : cocycle_two_sphere_class_resp (1 : M) ≈S
      (two_sphere_base Z (two_cocycle_simplex_unit 0) : Q).
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_class_β.
  symmetry. apply cocycle_constant_triangle_value.
Defined.

End SphereMonoid.

(** ** Group Inverses and Commutativity

    Strengthen the coefficient monoid to a group to encode inverse labels.
    The chosen class group inherits exactly the monoid constructed above.
    Commutativity is a separate property on that same selected monoid. *)

(** ** 群逆与交换性

    将系数幺半群加强为群，以编码逆标签。选定类群恰继承上面构造的幺半群。
    交换性是同一个选定幺半群上的独立性质。 *)

Section SphereGroup.
Universes u p.
Context {M : SetC} `{HG : !Group M}.

Let Z
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

Let Q
  : SetC
  := TwoSphereClassS Z (two_cocycle_simplex_unit 0).

(** Encode the inverse coefficient, retaining a freely labelled triangle. *)

(** 编码逆系数，保留一个自由标记三角形。 *)

Definition cocycle_two_sphere_inv (x : Q)
  : Q
  := cocycle_two_sphere_class_resp
      (cocycle_two_sphere_class_value_resp x)⁻¹.

(** Evaluation preserves the selected inverse. *)

(** 求值保持选定逆。 *)

Lemma cocycle_two_sphere_inv_value (x : Q)
  : cocycle_two_sphere_class_value_resp (cocycle_two_sphere_inv x) ≈S
      (cocycle_two_sphere_class_value_resp x)⁻¹.
Proof. apply cocycle_two_sphere_class_β. Defined.

(** The encoded inverse respects generated class equality. *)

(** 编码逆保持生成类相等。 *)

Global Instance cocycle_two_sphere_inv_proper
  : Proper ([≈S] ==> [≈S]) cocycle_two_sphere_inv.
Proof.
  intros x y H. apply func_proper. apply group_inv_proper.
  apply func_proper. exact H.
Defined.

(** A left inverse in the already selected class monoid. *)

(** 已选定类幺半群中的左逆。 *)

Lemma cocycle_two_sphere_inv_l (x : Q)
  : cocycle_two_sphere_mul (cocycle_two_sphere_inv x) x ≈S
      (two_sphere_base Z (two_cocycle_simplex_unit 0) : Q).
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_mul_value, cocycle_two_sphere_inv_value,
    group_inv_l.
  symmetry. apply cocycle_constant_triangle_value.
Defined.

(** A right inverse for the same unit and multiplication. *)

(** 同一单位及乘法下的右逆。 *)

Lemma cocycle_two_sphere_inv_r (x : Q)
  : cocycle_two_sphere_mul x (cocycle_two_sphere_inv x) ≈S
      (two_sphere_base Z (two_cocycle_simplex_unit 0) : Q).
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_mul_value, cocycle_two_sphere_inv_value,
    group_inv_r.
  symmetry. apply cocycle_constant_triangle_value.
Defined.

(** Explicitly enable this group; import alone selects no structure. *)

(** 显式启用这个群；单纯导入不选择结构。 *)

Program Definition cocycle_two_sphere_Group
  : Group Q
  :=
  {|GroupM := cocycle_two_sphere_Monoid
  ; group_inv := cocycle_two_sphere_inv
  ; group_inv_l := cocycle_two_sphere_inv_l
  ; group_inv_r := cocycle_two_sphere_inv_r
  |}.

(** Encoding coefficients also preserves their inverses. *)

(** 编码系数也保持其逆。 *)

Lemma cocycle_two_sphere_class_inv (a : M)
  : cocycle_two_sphere_class_resp a⁻¹ ≈S
      cocycle_two_sphere_inv (cocycle_two_sphere_class_resp a).
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_inv_value.
  repeat rewrite cocycle_two_sphere_class_β. reflexivity.
Defined.

End SphereGroup.

(** ** Commutative Class Monoids

    Only commutativity of the selected coefficient monoid is needed here;
    inverses are not used in the proof. *)

(** ** 交换类幺半群

    此处只需选定系数幺半群的交换性，证明不使用逆。 *)

Section SphereCommutativity.
Universes u p.
Context {M : SetC} `{HM : !Monoid M} `{HC : !IsCommutativeMonoid M}.

Let Z
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

(** Commutativity on the same selected class monoid. *)

(** 同一选定类幺半群上的交换性。 *)

Program Definition cocycle_two_sphere_IsCommutativeMonoid
  : @IsCommutativeMonoid
      (TwoSphereClassS Z (two_cocycle_simplex_unit 0))
      cocycle_two_sphere_Monoid
  :=
  {|monoid_mul_comm x y := _
  |}.
Next Obligation.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  change (cocycle_two_sphere_class_value_resp (cocycle_two_sphere_mul x y) ≈S
    cocycle_two_sphere_class_value_resp (cocycle_two_sphere_mul y x)).
  repeat rewrite cocycle_two_sphere_mul_value. apply monoid_mul_comm.
Defined.

End SphereCommutativity.
