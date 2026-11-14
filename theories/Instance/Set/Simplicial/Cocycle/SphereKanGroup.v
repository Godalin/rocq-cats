From Cats Require Export
  Instance.Set.Simplicial.Cocycle.SphereGroup
  Instance.Set.Simplicial.Homotopy.SphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope monoid_scope.

(** * Comparing Kan and Coefficient Sphere Operations

    Two constructions now live on the same cocycle sphere class setoid:
    the generic operation reads an actual Kan filler, while the earlier
    operation encodes the product coefficient. The existing theorem
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.SphereGroup.cocycle_two_sphere_composite_unique}
    {%[cocycle_two_sphere_composite_unique]%}% compares their outputs,
    because the generic operation retains an actual composite tetrahedron.
    This needs only a monoid and the explicit multiplication filler choice.

    Thus the existing classification maps preserve the generic product,
    as well as the constant unit. The original β/η laws and common-upward-
    lift isomorphism from
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Sphere.cocycle_two_sphere_class_iso}
    {%[cocycle_two_sphere_class_iso]%}% are reused unchanged. Carrier and
    equality sizes are raised independently when a common SetCat is needed;
    none of the class witnesses is resized downward.

    For group coefficients, general inverse uniqueness compares the actual
    left candidate with the encoded coefficient inverse. For commutative
    coefficients, the generic selected class monoid is commutative too.
    These are model comparisons, not a proof of commutativity for every
    Kan object or an identification with general π₂. *)

(** * 比较 Kan 与系数球面运算

    同一个 cocycle 球面类广集现有两种构造：通用运算读取实际 Kan 填充，先前
    运算编码乘积系数。既有定理
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.SphereGroup.cocycle_two_sphere_composite_unique}
    {%[cocycle_two_sphere_composite_unique]%}% 比较两者的输出，因为通用运算
    保留实际合成四面体。这里只需幺半群及显式乘法填充选择。

    因此，既有分类映射保持通用乘法及常值单位。原有 β／η 律及共同向上提升
    同构
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Sphere.cocycle_two_sphere_class_iso}
    {%[cocycle_two_sphere_class_iso]%}% 原样复用。需要共同 SetCat 时独立提升
    载体与相等大小，不向下重设类见证大小。

    对群系数，一般逆唯一性将实际左候选与编码系数逆比较。对交换系数，通用
    选定类幺半群也交换。这些是模型比较，不证明任意 Kan 对象的交换性，也不
    识别一般 π₂。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
Q\times Q \arrow[r,"\mu_{\mathrm{Kan}}"]
  \arrow[d,"{v\times v}"'] & Q \arrow[d,"v"] \\
M\times M \arrow[r,"\cdot"'] & M
\end{tikzcd}
\qquad $v=\overline{c}_{012},\quad e_Q=b_2.$
\end{center}%
*)

(** ** Comparing Products Without Four-Dimensional Choices

    Fix a coefficient monoid and independent ambient simplex sizes.
    The retained tetrahedron suffices to compare the two products; no
    full Kan or dimension-four choice is required here. *)

(** ** 无需四维选择的乘积比较

    固定系数幺半群及独立环境单形大小。保留四面体即足以比较两个乘积，此处
    不要求完整 Kan 或四维选择。 *)

Section KanProducts.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}.

Let Z
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

Let Q
  : SetC
  := TwoSphereClassS Z (two_cocycle_simplex_unit 0).

(** Any multiplication choice yields the coefficient-defined product class. *)

(** 任意乘法选择均给出系数定义的乘积类。 *)

Lemma cocycle_kan_mul_eq (H : HasHornFillers Z 3 fin_first⁺⁺) (x y : Q)
  : two_sphere_kan_mul Z (two_cocycle_simplex_unit 0) H x y ≈S
      cocycle_two_sphere_mul x y.
Proof.
  exact (cocycle_two_sphere_composite_unique x y _
    (TwoSphereKanMulComposite Z (two_cocycle_simplex_unit 0) H x y)).
Defined.

(** The existing decoder preserves the actual selected multiplication. *)

(** 既有读取映射保持实际选定乘法。 *)

Lemma cocycle_kan_mul_value (H : HasHornFillers Z 3 fin_first⁺⁺) (x y : Q)
  : cocycle_two_sphere_class_value_resp
      (two_sphere_kan_mul Z (two_cocycle_simplex_unit 0) H x y) ≈S
      cocycle_two_sphere_class_value_resp x ⋅
        cocycle_two_sphere_class_value_resp y.
Proof.
  transitivity (cocycle_two_sphere_class_value_resp (cocycle_two_sphere_mul x y)).
  - apply func_proper. exact (cocycle_kan_mul_eq H x y).
  - apply cocycle_two_sphere_mul_value.
Defined.

(** The existing encoder preserves the product in the opposite direction.
    Its unit and both round trips are the already proved classification laws. *)

(** 既有编码映射在反方向保持乘积；其单位及两个往返律就是已证明的分类定律。 *)

Lemma cocycle_kan_class_mul (H : HasHornFillers Z 3 fin_first⁺⁺) (a b : M)
  : cocycle_two_sphere_class_resp (a ⋅ b) ≈S
      two_sphere_kan_mul Z (two_cocycle_simplex_unit 0) H
        (cocycle_two_sphere_class_resp a) (cocycle_two_sphere_class_resp b).
Proof.
  transitivity (cocycle_two_sphere_mul (cocycle_two_sphere_class_resp a)
    (cocycle_two_sphere_class_resp b)).
  - apply cocycle_two_sphere_class_mul.
  - symmetry. apply cocycle_kan_mul_eq.
Defined.

End KanProducts.

(** ** Inverse Comparison by Existing Group Uniqueness

    Fix group coefficients and independent ambient sizes. Only the actual
    left-candidate choice is needed. Compare its product equation inside
    the already constructed coefficient-defined class group. *)

(** ** 经既有群唯一性比较逆

    固定群系数及独立环境大小。只需实际左候选的选择；在已构造的系数定义类群
    内比较其乘积方程。 *)

Section KanInverses.
Universes u p.
Context {M : SetC} `{HG : !Group M}.

Let Z
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

Let Q
  : SetC
  := TwoSphereClassS Z (two_cocycle_simplex_unit 0).

(** General group uniqueness identifies the chosen left candidate with
    the coefficient-defined inverse. No multiplication or right-candidate
    choice, dimension-four selection or commutativity is required. *)

(** 一般群唯一性将选定左候选识别为系数定义逆；不要求乘法或右候选选择、四维
    选择或交换性。 *)

Lemma cocycle_kan_left_inverse_eq
    (K : HasHornFillers Z 3 fin_first⁺⁺⁺) (x : Q)
  : ((@SphereKanLeftInverse Z (two_cocycle_simplex_unit 0) K x).1 : Q) ≈S
      cocycle_two_sphere_inv x.
Proof.
  refine (@group_inv_unique Q cocycle_two_sphere_Group x
    (@SphereKanLeftInverse Z (two_cocycle_simplex_unit 0) K x).1 _).
  symmetry. exact (cocycle_two_sphere_composite_unique _ x _
    (@SphereKanLeftInverse Z (two_cocycle_simplex_unit 0) K x).2).
Defined.

(** Decoding that same actual inverse gives the inverse coefficient. *)

(** 读取同一个实际逆得到逆系数。 *)

Lemma cocycle_kan_left_inverse_value
    (K : HasHornFillers Z 3 fin_first⁺⁺⁺) (x : Q)
  : cocycle_two_sphere_class_value_resp
      (@SphereKanLeftInverse Z (two_cocycle_simplex_unit 0) K x).1 ≈S
      (cocycle_two_sphere_class_value_resp x)⁻¹.
Proof.
  transitivity (cocycle_two_sphere_class_value_resp (cocycle_two_sphere_inv x)).
  - apply func_proper. exact (cocycle_kan_left_inverse_eq K x).
  - apply cocycle_two_sphere_inv_value.
Defined.

End KanInverses.

(** ** Commutativity of the Same Generic Class Monoid

    Fix only commutative monoid coefficients. The raw product law needs
    only its dimension-three choice; packaging the property on the exact
    generic class monoid also supplies that monoid's explicit choices. *)

(** ** 同一通用类幺半群的交换性

    仅固定交换幺半群系数。原始乘积律只需自身三维选择；在完全相同的通用类
    幺半群上打包此性质时，再提供该幺半群的显式选择。 *)

Section KanCommutativity.
Universes u p.
Context {M : SetC} `{HM : !Monoid M} `{HC : !IsCommutativeMonoid M}.

Let Z
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

Let Q
  : SetC
  := TwoSphereClassS Z (two_cocycle_simplex_unit 0).

(** Transfer the existing model commutativity law across product comparison. *)

(** 经乘积比较传递既有模型交换律。 *)

Lemma cocycle_kan_mul_comm (H : HasHornFillers Z 3 fin_first⁺⁺) (x y : Q)
  : two_sphere_kan_mul Z (two_cocycle_simplex_unit 0) H x y ≈S
      two_sphere_kan_mul Z (two_cocycle_simplex_unit 0) H y x.
Proof.
  transitivity (cocycle_two_sphere_mul x y); [apply cocycle_kan_mul_eq |].
  transitivity (cocycle_two_sphere_mul y x).
  - exact (@monoid_mul_comm Q cocycle_two_sphere_Monoid
      cocycle_two_sphere_IsCommutativeMonoid x y).
  - symmetry. apply cocycle_kan_mul_eq.
Defined.

Context `{HX2 : !HasHornFillers Z 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers Z 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers Z 4 fin_first⁺⁺⁺⁺}.

(** The commutativity property is tied to the generic monoid's exact
    selected multiplication; it selects no second structure. *)

(** 交换性性质绑定到通用幺半群中完全相同的选定乘法，不另选第二结构。 *)

Program Definition cocycle_kan_IsCommutativeMonoid
    (H : HasHornFillers Z 3 fin_first⁺⁺)
  : @IsCommutativeMonoid Q
      (TwoSphereClassMonoid Z (two_cocycle_simplex_unit 0) H)
  :=
  {|monoid_mul_comm := cocycle_kan_mul_comm H
  |}.

End KanCommutativity.
