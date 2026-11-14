From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereSecondTransport
  Algebra.Magma.Core.
From Cats Require Import
  Instance.Set.Magma.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope magma_scope.

(** * A Binary Operation on Sphere Classes

    A representative x is still an actual based triangle; its class
    equality is the generated tetrahedron relation, not native equality.
    The preceding
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFirstTransport.two_sphere_composite_first_class}
    {%[two_sphere_composite_first_class]%}% and
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereSecondTransport.two_sphere_composite_second_class}
    {%[two_sphere_composite_second_class]%}% transport composite witnesses
    along that relation in each input separately. Compose those transports:
    first change x to x', then y to y', retaining the same output z.

    Given another composite of x' and y' with output z', the existing
    four-horn comparison identifies z and z' in class equality. Thus the
    result depends on neither input representative nor the chosen
    three-horn filler. No equality of the composite tetrahedra is needed.
    In the diagram, horizontal arrows are supplied generated input
    equalities, while the vertical arrows record actual composites.

    This gives a magma: a respectful binary operation. Associativity,
    units and inverses require further arguments. The next chapter's
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereUnit.two_sphere_kan_mul_unit_l}
    {%[two_sphere_kan_mul_unit_l]%}% begins with the constant unit and
    products with inverse candidates. This module does not yet identify
    a general Kan homotopy group. *)

(** * 球面类上的二元运算

    代表 x 仍是实际带基点三角形，其类相等是生成四面体关系，不是原生相等。
    前两章的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFirstTransport.two_sphere_composite_first_class}
    {%[two_sphere_composite_first_class]%}% 及
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereSecondTransport.two_sphere_composite_second_class}
    {%[two_sphere_composite_second_class]%}% 分别沿两个输入运输合成见证。
    现在将运输接起来：先将 x 改为 x'，再将 y 改为 y'，始终保留同一个输出 z。

    若另有 x' 与 y' 的一份合成，输出为 z'，既有四维 horn 比较便给出 z 与 z'
    的类相等。因此结果既不依赖输入代表，也不依赖所选三维 horn 填充；无须
    等同合成四面体。下图横边是给定的生成输入相等，竖边记录实际合成。

    这给出原群，即保相等二元运算。结合律、单位元及逆仍需进一步论证。下一章的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereUnit.two_sphere_kan_mul_unit_l}
    {%[two_sphere_kan_mul_unit_l]%}% 先证明常值单位及逆候选的乘积律。此模块
    尚不识别一般 Kan 同伦群。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
(x,y) \arrow[r,"{(E_x,E_y)}"] \arrow[d,"w"']
  & (x',y') \arrow[d,"{w'}"] \\
z \arrow[r,dashed,"{[z]=[z']}"'] & z'
\end{tikzcd}
\end{center}%
*)

(** ** Changing Both Inputs

    Fix the simplicial setoid, its base vertex and only the dimension-four
    horn choices used by the integrated transports and output comparison.
    No dimension-three choice, full Kan structure, respectful selection or
    uniqueness is needed for supplied composite witnesses. *)

(** ** 同时改变两个输入

    固定单纯广集、基点及已集成运输和输出比较所需的四维 horn 选择。对给定
    合成见证，不要求三维选择、完整 Kan 结构、选择保相等或唯一性。 *)

Section BinaryClassTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.

(** Two generated input equalities give two-way composite transport with
    precisely the same output representative. The transformations do not
    carry inverse equations on tetrahedra or witness fields. *)

(** 两个生成输入相等给出双向合成运输，保留完全相同的输出代表；转换不带有
    四面体或见证字段上的互逆方程。 *)

Definition two_sphere_composite_class
    {x x' y y' : TwoSphereS X b}
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y') (z : TwoSphereS X b)
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y' z.
Proof.
  split; intros H.
  - exact (fst (two_sphere_composite_second_class X b F x' z)
      (fst (two_sphere_composite_first_class X b E y z) H)).
  - exact (snd (two_sphere_composite_first_class X b E y z)
      (snd (two_sphere_composite_second_class X b F x' z) H)).
Defined.

(** Arbitrary supplied composites of class-equal input pairs have
    class-equal outputs. The original output is transported unchanged
    before using the fixed-input four-horn comparison. *)

(** 类相等输入对的任意给定合成具有类相等输出。先保持原输出不变地运输，
    再使用固定输入的四维 horn 比较。 *)

Lemma two_sphere_composite_output_class_eq
    {x x' y y' z z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x' y' z')
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : (z : TwoSphereClassS X b) ≈S z'.
Proof.
  exact (two_sphere_composite_output_eq X b
    (fst (two_sphere_composite_class E F z) H) K).
Defined.

(** Both selected outputs respect both generated inputs, including when
    the two dimension-three selections are independent. *)

(** 两个选定输出均保持两个生成输入的相等，即使两份三维选择相互独立。 *)

Lemma two_sphere_kan_composite_class_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    {x x' y y' : TwoSphereS X b}
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : ((@SphereKanComposite X b H x y).1 : TwoSphereClassS X b) ≈S
      (@SphereKanComposite X b K x' y').1.
Proof.
  exact (two_sphere_composite_output_class_eq
    (@SphereKanComposite X b H x y).2
    (@SphereKanComposite X b K x' y').2 E F).
Defined.

End BinaryClassTransport.

(** ** An Explicitly Selected Magma

    Fix the same setoid and vertex with the three required four-horn
    selections. A dimension-three selection is explicit data to each
    operation/structure, never a global instance. Reuse the existing
    [Magma] hierarchy and product-map construction; no stronger laws are
    stored, and the product computes exactly the selected Kan output. *)

(** ** 显式选择的原群

    固定同样的广集及顶点和三个所需四维 horn 选择。每个运算或结构显式接收
    三维选择，不注册全局实例。复用既有 [Magma] 层级和积映射构造，不保存更强
    定律，乘积准确计算选定 Kan 输出。 *)

Section ClassMagma.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.

(** The binary operation retains the chosen three-horn computation. *)

(** 二元运算保留选定三维 horn 的计算。 *)

Definition two_sphere_kan_mul (H : HasHornFillers X 3 fin_first⁺⁺)
    (x y : TwoSphereClassS X b)
  : TwoSphereClassS X b
  := (@SphereKanComposite X b H x y).1.

(** Its geometric witness is the actual chosen composite tetrahedron. *)

(** 其几何见证就是实际选定的合成四面体。 *)

Definition TwoSphereKanMulComposite
    (H : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereClassS X b)
  : TwoSphereComposite X b x y (two_sphere_kan_mul H x y)
  := (@SphereKanComposite X b H x y).2.

(** The full generated relation is respected in both arguments. *)

(** 两个参数均保持完整生成关系。 *)

Global Instance two_sphere_kan_mul_proper
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Proper ([≈S] ==> [≈S] ==> [≈S]) (two_sphere_kan_mul H).
Proof.
  intros x x' E y y' F.
  exact (two_sphere_kan_composite_class_eq X b H H E F).
Defined.

(** Package only a respectful multiplication on the named class setoid.
    Importing this definition does not enable any chosen model structure. *)

(** 在具名类广集上只打包保相等乘法；导入此定义不启用任何选定模型结构。 *)

Program Definition TwoSphereClassMagma
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Magma (TwoSphereClassS X b)
  :=
  {|magma_mul := two_sphere_kan_mul H
  |}.

(** The two magma multiplications agree as respectful maps from the
    product setoid. No equality of selections or structure records occurs. *)

(** 两个原群乘法作为积广集出发的保相等映射一致，不等同选择或结构记录。 *)

Lemma two_sphere_class_magma_choice_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺)
  : set_magma_mul_resp (TwoSphereClassMagma H) ≈f
      set_magma_mul_resp (TwoSphereClassMagma K).
Proof.
  intros [x y]. exact (two_sphere_kan_composite_choice_eq X b H K x y).
Defined.

(** The existing first-input partial map is exactly right multiplication
    for this choice, compared pointwise in specified class equality. *)

(** 既有第一输入偏映射正是此选择的右乘，按指定类相等逐点比较。 *)

Lemma two_sphere_class_magma_first_eq
    (H : HasHornFillers X 3 fin_first⁺⁺) (y : TwoSphereClassS X b)
  : @magma_mul_r_resp _ (TwoSphereClassMagma H) y ≈f
      two_sphere_kan_composite_first_resp X b H y.
Proof. intros x. reflexivity. Defined.

(** The second-input partial map is similarly left multiplication. *)

(** 第二输入偏映射同样就是左乘。 *)

Lemma two_sphere_class_magma_second_eq
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : @magma_mul_l_resp _ (TwoSphereClassMagma H) x ≈f
      two_sphere_kan_composite_second_resp X b H x.
Proof. intros y. reflexivity. Defined.

End ClassMagma.
