From Cats Require Export
  Algebra.Group.Core.

Local Open Scope monoid_scope.

(** * Solving Multiplication Equations

    In a group, knowing a product and either factor determines the other.
    The selected solutions of [a ⋅ x ≈S b] and [x ⋅ a ≈S b] are respectively
    [a⁻¹ ⋅ b] and [b ⋅ a⁻¹]. They use the inverse already stored by
    %\coqref{Cats.Algebra.Group.Core.Group}{%[Group]%}%.
    No commutativity, native equality or choice principle is needed.

    The two arrows below are actual respectful functions on the same set
    [G]. Their composites equal the identity pointwise, by associativity
    and the two inverse laws. Thus multiplying by [a] is reversible even
    when [G] is not commutative. The forward map is
    %\coqref{Cats.Algebra.Magma.Core.magma mul l resp}
    {%[magma_mul_l_resp]%}%; its inverse is
    %\coqref{Cats.Algebra.Group.Equation.group mul l solve resp}
    {%[group_mul_l_solve_resp]%}% below.

    For a later equation [p ⋅ q ≈S r ⋅ s], fixing three labels reduces
    solving for the fourth to one of these two equations. This algebraic
    step alone does not construct a compatible family of simplicial faces. *)

(** * 求解乘法方程

    在群中，已知乘积和一个因子即可确定另一个。[a ⋅ x ≈S b] 与
    [x ⋅ a ≈S b] 的选定解分别为 [a⁻¹ ⋅ b] 与 [b ⋅ a⁻¹]，复用
    %\coqref{Cats.Algebra.Group.Core.Group}{%[Group]%}% 已保存的逆运算，
    不需要交换律、原生相等或选择原理。

    图中两条箭头是同一个广集 [G] 上实际的保相等函数。由结合律和两条逆律，
    它们的复合逐点等于恒等函数。因此，即使 [G] 不交换，乘以 [a] 也可逆。
    正向映射为 %\coqref{Cats.Algebra.Magma.Core.magma mul l resp}
    {%[magma_mul_l_resp]%}%，逆映射为下方的
    %\coqref{Cats.Algebra.Group.Equation.group mul l solve resp}
    {%[group_mul_l_solve_resp]%}%。

    对后续的方程 [p ⋅ q ≈S r ⋅ s]，固定三个标签后，求第四个就归结为这两类
    方程之一。这一步代数求解本身尚未构造相容的单纯形面族。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge]
G \arrow[r,shift left=1,"{x\mapsto a\cdot x}"] &
G \arrow[l,shift left=1,"{y\mapsto a^{-1}\cdot y}"]
\end{tikzcd}
\end{center}%
*)

(** ** Cancellation and Selected Solutions

    Fix a setoid [G] with its chosen group structure. Cancellation and
    uniqueness use the equality of [G], and solution witnesses stay in [Type]. *)

(** ** 消去律与选定解

    固定带选定群结构的广集 [G]。消去与唯一性使用 [G] 的相等，解的见证
    保留在 [Type] 中。 *)

Section Equations.
Context {G : SetC} `{HG : !Group G}.

(** Cancel a fixed left factor by multiplying with its selected inverse. *)

(** 乘以选定的逆，消去固定的左因子。 *)

Lemma group_mul_cancel_l (a x y : G) (H : a ⋅ x ≈S a ⋅ y)
  : x ≈S y.
Proof.
  transitivity (a⁻¹ ⋅ (a ⋅ x)).
  - symmetry. rewrite <- semigroup_assoc, group_inv_l, monoid_unit_l.
    reflexivity.
  - rewrite H, <- semigroup_assoc, group_inv_l, monoid_unit_l. reflexivity.
Defined.

(** Cancel a fixed right factor; no exchange of factors is used. *)

(** 消去固定的右因子，不交换因子。 *)

Lemma group_mul_cancel_r (a x y : G) (H : x ⋅ a ≈S y ⋅ a)
  : x ≈S y.
Proof.
  transitivity ((x ⋅ a) ⋅ a⁻¹).
  - symmetry. rewrite semigroup_assoc, group_inv_r, monoid_unit_r.
    reflexivity.
  - rewrite H, semigroup_assoc, group_inv_r, monoid_unit_r. reflexivity.
Defined.

(** The inverse on the left gives an actual solution of left multiplication. *)

(** 在左侧乘以逆，给出左乘方程的实际解。 *)

Lemma group_mul_l_solution (a b : G)
  : a ⋅ (a⁻¹ ⋅ b) ≈S b.
Proof.
  rewrite <- semigroup_assoc, group_inv_r, monoid_unit_l. reflexivity.
Defined.

(** The inverse on the right solves right multiplication. *)

(** 在右侧乘以逆，解出右乘方程。 *)

Lemma group_mul_r_solution (a b : G)
  : (b ⋅ a⁻¹) ⋅ a ≈S b.
Proof.
  rewrite semigroup_assoc, group_inv_l, monoid_unit_r. reflexivity.
Defined.

(** Select the left-multiplication solution, its equation and its full
    uniqueness property. The first projection computes to [a⁻¹ ⋅ b]. *)

(** 选取左乘方程的解、方程见证及完整唯一性；第一投影计算为 [a⁻¹ ⋅ b]。 *)

Definition GroupMulLSolution (a b : G)
  : ∃ x : G, is_unique (R := carrier_equiv G) (λ x, a ⋅ x ≈S b) x.
Proof.
  exists (a⁻¹ ⋅ b).
  refine {|this := _
          ; that := _
          |}.
  - apply group_mul_l_solution.
  - intros x H. apply (group_mul_cancel_l a).
    rewrite H. symmetry. apply group_mul_l_solution.
Defined.

(** Select the right-multiplication solution in the same specified equality.
    Its first projection computes to [b ⋅ a⁻¹]. *)

(** 在同一指定相等中选取右乘方程的解；第一投影计算为 [b ⋅ a⁻¹]。 *)

Definition GroupMulRSolution (a b : G)
  : ∃ x : G, is_unique (R := carrier_equiv G) (λ x, x ⋅ a ≈S b) x.
Proof.
  exists (b ⋅ a⁻¹).
  refine {|this := _
          ; that := _
          |}.
  - apply group_mul_r_solution.
  - intros x H. apply (group_mul_cancel_r a).
    rewrite H. symmetry. apply group_mul_r_solution.
Defined.

(** Varying the right-hand side preserves its equality. The selected inverse
    of the fixed factor is reused, rather than selected again. *)

(** 改变方程右端保持其相等；复用固定因子已选定的逆，不重新作选择。 *)

Program Definition group_mul_l_solve_resp (a : G)
  : G →r G
  :=
  {|func b := (GroupMulLSolution a b).1
  |}.
Next Obligation.
  intros b c H. apply magma_mul_proper; [reflexivity | exact H].
Defined.

(** Respectful solution map for a fixed right factor. *)

(** 固定右因子时的保相等求解映射。 *)

Program Definition group_mul_r_solve_resp (a : G)
  : G →r G
  :=
  {|func b := (GroupMulRSolution a b).1
  |}.
Next Obligation.
  intros b c H. apply magma_mul_proper; [exact H | reflexivity].
Defined.

(** Changing the fixed left factor also preserves the solution map. *)

(** 改变固定左因子也保持求解映射的相等。 *)

Global Instance group_mul_l_solve_proper
  : Proper (carrier_equiv G ==> FunEq) group_mul_l_solve_resp.
Proof.
  intros a a' H b. cbn. apply magma_mul_proper;
    [apply group_inv_proper; exact H | reflexivity].
Defined.

(** Changing the fixed right factor preserves the right-solution map. *)

(** 改变固定右因子保持右乘求解映射的相等。 *)

Global Instance group_mul_r_solve_proper
  : Proper (carrier_equiv G ==> FunEq) group_mul_r_solve_resp.
Proof.
  intros a a' H b. cbn. apply magma_mul_proper;
    [reflexivity | apply group_inv_proper; exact H].
Defined.

(** Multiplying the selected left solution recovers the right-hand side. *)

(** 对选定左乘解作乘法，恢复方程右端。 *)

Lemma group_mul_l_solve_β (a : G)
  : magma_mul_l_resp a ∘r group_mul_l_solve_resp a ≈f id_resp.
Proof. intro b. exact (@this _ _ _ _ _ (GroupMulLSolution a b).2). Defined.

(** Solving after left multiplication recovers the input, by uniqueness. *)

(** 由唯一性，先左乘再求解即可恢复输入。 *)

Lemma group_mul_l_solve_η (a : G)
  : group_mul_l_solve_resp a ∘r magma_mul_l_resp a ≈f id_resp.
Proof.
  intro x. symmetry.
  apply (@that _ _ _ _ _ (GroupMulLSolution a (a ⋅ x)).2 x).
  reflexivity.
Defined.

(** The right-multiplication solution has the same evaluation law. *)

(** 右乘方程的解满足同样的求值律。 *)

Lemma group_mul_r_solve_β (a : G)
  : magma_mul_r_resp a ∘r group_mul_r_solve_resp a ≈f id_resp.
Proof. intro b. exact (@this _ _ _ _ _ (GroupMulRSolution a b).2). Defined.

(** Uniqueness also gives the right-multiplication round trip. *)

(** 唯一性也给出右乘情形的往返律。 *)

Lemma group_mul_r_solve_η (a : G)
  : group_mul_r_solve_resp a ∘r magma_mul_r_resp a ≈f id_resp.
Proof.
  intro x. symmetry.
  apply (@that _ _ _ _ _ (GroupMulRSolution a (x ⋅ a)).2 x).
  reflexivity.
Defined.

End Equations.
