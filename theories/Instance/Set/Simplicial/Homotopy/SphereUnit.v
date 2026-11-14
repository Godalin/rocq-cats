From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereMagma.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Units and Products with Inverse Candidates

    The constant triangle is a unit for the selected class multiplication.
    This follows from actual composite tetrahedra: [s_1 x] witnesses a
    left unit, and [s_2 x] a right unit. Their faces are determined by the
    simplicial identities and the boundary of x; no horn choice is needed
    to construct them. In the diagrams b_2 denotes the constant triangle.

    The existing four-horn output comparison then relates any selected
    product to these unit outputs. The same argument applies to the
    already constructed
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKan.SphereKanLeftInverse}
    {%[SphereKanLeftInverse]%}% and
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKan.SphereKanRightInverse}
    {%[SphereKanRightInverse]%}%: each candidate's corresponding product
    is the constant class, even with independent multiplication choices.

    Only missing-face-two four-horn selection is required for comparison.
    These laws do not yet prove associativity, identify the two inverse
    candidates, or make either candidate a respectful class map. Group
    packaging must wait for the remaining laws and general inverse
    uniqueness; we do not introduce an alternative algebra hierarchy.
    Next,
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereAssociativity.two_sphere_kan_mul_assoc}
    {%[two_sphere_kan_mul_assoc]%}% proves associativity by an actual
    four-horn while retaining the same selected multiplication. *)

(** * 单位与逆候选的乘积

    常值三角形是选定类乘法的单位。这由实际合成四面体给出：[s_1 x] 见证左
    单位，[s_2 x] 见证右单位。它们的面由单纯恒等式及 x 的边界确定，构造时
    无需任何 horn 选择。下图 b_2 表示常值三角形。

    既有四维 horn 输出比较随后将任意选定乘积与这些单位输出联系起来。同样的
    论证适用于已构造的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKan.SphereKanLeftInverse}
    {%[SphereKanLeftInverse]%}% 和
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKan.SphereKanRightInverse}
    {%[SphereKanRightInverse]%}%：各候选对应的乘积为常值类，即使乘法选择独立。

    比较只需四维缺第二面的选择。这些定律尚不证明结合律、识别两个逆候选，
    或使任一候选成为保相等类映射。群的打包须等待其余定律及一般逆唯一性，
    不在这里引入另一套代数层级。接下来的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereAssociativity.two_sphere_kan_mul_assoc}
    {%[two_sphere_kan_mul_assoc]%}% 通过实际四维 horn 证明结合律，保留同一份
    选定乘法。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
b_2 & s_1x \arrow[l,"d_3"'] \arrow[r,"d_1"] \arrow[d,"d_2"'] & x \\
& x &
\end{tikzcd}
\qquad
\begin{tikzcd}[column sep=large,row sep=large]
x & s_2x \arrow[l,"d_3"'] \arrow[r,"d_1"] \arrow[d,"d_2"'] & b_2 \\
& x &
\end{tikzcd}
\qquad $d_0s_1x=d_0s_2x=b_2.$
\end{center}%
*)

(** ** Unit Tetrahedra Without Choices

    Fix a simplicial setoid with independent simplex carrier/equality
    sizes and a base vertex. Reuse the already proved degeneracy boundary
    equations; the two unit witnesses retain their actual tetrahedra. *)

(** ** 无需选择的单位四面体

    固定单形载体／相等大小独立的单纯广集及基点。复用已证明的退化边界方程；
    两个单位见证保留实际四面体。 *)

Section UnitComposites.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** The middle degeneracy composes the constant sphere with x to x. *)

(** 中间退化将常值球面与 x 合成为 x。 *)

Definition SphereLeftUnitComposite (x : TwoSphereS X b)
  : TwoSphereComposite X b (two_sphere_base X b) x x.
Proof.
  exists (s[X; 2; fin_first⁺] x.1). split; [| split; [| split]].
  - exact (sphere_first_degenerate_zero X b x).
  - exact (simplex_face_degeneracy_id (X := X)
      (fin_first⁺ : Ordinal 2) x.1).
  - exact (simplex_face_degeneracy_next (X := X)
      (fin_first⁺ : Ordinal 2) x.1).
  - exact (sphere_first_degenerate_last X b x).
Defined.

(** The final degeneracy composes x with the constant sphere to x. *)

(** 最后退化将 x 与常值球面合成为 x。 *)

Definition SphereRightUnitComposite (x : TwoSphereS X b)
  : TwoSphereComposite X b x (two_sphere_base X b) x.
Proof.
  exists (s[X; 2; fin_first⁺⁺] x.1). split; [| split; [| split]].
  - exact (sphere_comparison_degenerate_low X b x fin_first).
  - exact (sphere_comparison_degenerate_low X b x fin_first⁺).
  - exact (simplex_face_degeneracy_id (X := X)
      (fin_first⁺⁺ : Ordinal 2) x.1).
  - exact (simplex_face_degeneracy_next (X := X)
      (fin_first⁺⁺ : Ordinal 2) x.1).
Defined.

End UnitComposites.

(** ** Class Laws with Only Output Comparison

    Fix the same ambient setoid and vertex, selecting only dimension-four
    missing-face-two fillers. Multiplication and each inverse candidate
    retain their separate explicit dimension-three choices. These laws
    apply before selecting a magma structure or proving associativity. *)

(** ** 仅用输出比较的类定律

    固定同样的环境广集及顶点，只选择四维缺第二面的填充。乘法及每侧逆候选
    保留各自显式三维选择。这些定律在选择原群结构或证明结合律之前即可使用。 *)

Section ClassUnitLaws.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.

(** Any selected multiplication has the constant sphere as a left unit. *)

(** 任意选定乘法都以常值球面为左单位。 *)

Lemma two_sphere_kan_mul_unit_l
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_base X b) x ≈S x.
Proof.
  exact (two_sphere_composite_output_eq X b
    (TwoSphereKanMulComposite X b H (two_sphere_base X b) x)
    (SphereLeftUnitComposite X b x)).
Defined.

(** The same constant sphere is also a right unit. *)

(** 同一个常值球面也是右单位。 *)

Lemma two_sphere_kan_mul_unit_r
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (two_sphere_base X b) ≈S x.
Proof.
  exact (two_sphere_composite_output_eq X b
    (TwoSphereKanMulComposite X b H x (two_sphere_base X b))
    (SphereRightUnitComposite X b x)).
Defined.

(** The already selected left candidate multiplies with x to the
    constant class. Only its own dimension-three missing-face-three choice
    is required, independently of the multiplication choice. *)

(** 已选左候选与 x 相乘为常值类；仅额外要求它自身三维缺第三面的选择，与
    乘法选择相互独立。 *)

Lemma two_sphere_kan_mul_inverse_l
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (@SphereKanLeftInverse X b K x).1 x ≈S
      (two_sphere_base X b : TwoSphereClassS X b).
Proof.
  exact (two_sphere_composite_output_eq X b
    (TwoSphereKanMulComposite X b H (@SphereKanLeftInverse X b K x).1 x)
    (@SphereKanLeftInverse X b K x).2).
Defined.

(** The right candidate similarly multiplies to the constant class,
    requiring only its dimension-three missing-face-one choice. *)

(** 右候选同样相乘为常值类，仅要求它三维缺第一面的选择。 *)

Lemma two_sphere_kan_mul_inverse_r
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (@SphereKanRightInverse X b K x).1 ≈S
      (two_sphere_base X b : TwoSphereClassS X b).
Proof.
  exact (two_sphere_composite_output_eq X b
    (TwoSphereKanMulComposite X b H x (@SphereKanRightInverse X b K x).1)
    (@SphereKanRightInverse X b K x).2).
Defined.

End ClassUnitLaws.
