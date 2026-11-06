(** * Limits: One Universal Property, Three Views

    This chapter connects cones, terminal objects and adjunctions. It assumes
    familiarity with categories, functors and natural transformations. Read
    the explanations in order; follow the linked identifiers for the complete
    library interfaces. All displayed Rocq commands and examples are checked.

    Throughout this library, sets are setoids. Strict equations mean their
    specified equality; an object's universal property determines it up to
    categorical isomorphism. These two comparisons have different roles. *)

(** * 极限：同一个泛性质的三种视角

    本章将锥、终对象和伴随联系起来，假定读者熟悉范畴、函子和自然变换。按顺序
    阅读叙述，通过标识符链接查看库的完整接口。全部展示的 Rocq 命令与示例均参与
    编译检查。

    本库中的集合是广集。严格方程指其指定相等；对象的泛性质则在范畴同构意义下
    确定该对象。这两种比较承担不同角色。 *)

From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Terminal
  Cat.Pullback
  Cat.Adjunction
  Cat.Limit.Core
  Cat.Limit.Adjunction
  Cat.Limit.Pullback.

(** ** 1. A cone is a compatible family of arrows

    Fix a shape [J], a category [C], and a diagram [D : Functor J C]. A cone
    with apex [X] gives one arrow [κ j : Hom X (D j)] for each vertex [j].
    Along every shape arrow [a : Hom i j], compatibility says
    [κ j ≈ fmap D a ∘ κ i].

    The triangle below commutes in the specified hom-setoid equality.
    This compatibility is exactly naturality of a transformation from the
    constant diagram at [X]. Consequently [X ⇒Δ D] is already a natural
    transformation type, and [cone_naturality] supplies the triangle equation. *)

(** ** 1. 锥是一个相容的箭头族

    固定形状 [J]、范畴 [C] 及图式 [D : Functor J C]。顶点为 [X] 的锥为每个
    位置 [j] 给出箭头 [κ j : Hom X (D j)]。沿每条形状箭头 [a : Hom i j]，
    相容性要求 [κ j ≈ fmap D a ∘ κ i]。

    下方三角图在指定 Hom 广集相等下交换。这恰好是从 [X] 上的常图式出发的
    自然变换的自然性。因此，[X ⇒Δ D] 已经是
    自然变换类型，[cone_naturality] 则给出三角形方程。 *)

(** @lang both
%
\[
\begin{tikzcd}[column sep=large, row sep=large]
  & X \arrow[dl, "\kappa_i"'] \arrow[dr, "\kappa_j"] & \\
  D(i) \arrow[rr, "D(a)"'] & & D(j)
\end{tikzcd}
\]
%
*)

Check @Cone.
Check @cone_naturality.

(** ** 2. What does a limit represent?

    A limiting cone [κ : L ⇒Δ D] is a universal compatible family. Every cone
    [μ : X ⇒Δ D] factors through it by a unique arrow [h : Hom X L]:
    [κ ∘Cone h ≈N μ]. The equation compares the legs pointwise. Uniqueness
    compares mediating arrows in their hom-setoid.

    The candidate property [is_limit κ] retains this mediator and its unique
    factorization. [HasLimit C D] additionally selects an apex, a cone and that
    property. This distinction lets us prove a property of an existing cone
    without first choosing a limit for every diagram. *)

(** ** 2. 极限表示什么？

    极限锥 [κ : L ⇒Δ D] 是泛的相容箭头族。每个锥 [μ : X ⇒Δ D] 都经唯一箭头
    [h : Hom X L] 分解，满足 [κ ∘Cone h ≈N μ]。这个方程逐点比较锥腿；唯一性
    在 Hom 广集中比较中介箭头。

    候选性质 [is_limit κ] 保留中介及其唯一分解。[HasLimit C D] 还选定顶点、锥
    及该性质。这样就可以先证明某个已有锥的泛性质，而不必预先为全部图式选择极限。 *)

Check @is_limit.
Check @HasLimit.

(** ** 3. Using the chosen mediator

    With [HL : HasLimit C D], the apex is [lim D], its cone is [πlim[D]],
    and the mediator of [μ] is [lim⟨μ⟩]. The beta equation recovers the input
    cone. The eta equation recovers any arrow from the cone it induces.

    The first example extracts one component of beta. The second uses the
    uniqueness part of the universal property; no comparison of proof fields
    or equality of functions is involved. *)

(** ** 3. 使用选定中介

    给定 [HL : HasLimit C D]，顶点记作 [lim D]，极限锥为 [πlim[D]]，[μ] 的中介
    为 [lim⟨μ⟩]。β 方程恢复输入锥，η 方程从一条箭头诱导的锥恢复这条箭头。

    第一个示例提取 β 的一个分量。第二个使用泛性质的唯一性部分；不需要比较证明
    字段，也不要求函数的原生相等。 *)

Section WorkingWithALimit.
Context {J C : Cat} {D : Functor J C} `{HL : !HasLimit C D}.

(** Each projection of the mediator recovers the corresponding leg. *)

(** 中介的每个投影都恢复对应锥腿。 *)

Example mediator_projection {X : @Ob C} (μ : X ⇒Δ D) (j : @Ob J)
  : πlim[D] j ∘ lim⟨μ⟩ ≈ μ j.
Proof. exact (limit_β μ j). Qed.

(** An arrow satisfying the factorization equation is the chosen mediator. *)

(** 满足分解方程的箭头等于选定中介。 *)

Example recognize_mediator {X : @Ob C} (μ : X ⇒Δ D)
    (h : Hom X (lim D)) (H : πlim[D] ∘Cone h ≈N μ)
  : h ≈ lim⟨μ⟩.
Proof. apply limit_lift_unique. exact H. Qed.

(** Exercise: equal cones should give equal mediators. The solution uses
    respectfulness of the universal operation, rather than unpacking cones. *)

(** 练习：相等的锥应给出相等中介。解答使用泛运算保持相等的性质，无需拆开锥。 *)

Example equal_cones_equal_mediators {X : @Ob C} (μ ν : X ⇒Δ D)
    (H : μ ≈N ν)
  : lim⟨μ⟩ ≈ lim⟨ν⟩.
Proof. apply limit_lift_proper. exact H. Qed.

End WorkingWithALimit.

(** ** 4. The terminal-object view

    Now place all cones over [D] in one category, [ConeCat D]. A morphism is
    an apex map commuting with the legs. The statement that every cone has a
    unique map to the limiting cone says exactly that this cone is terminal.

    [limit_iff_terminal] proves both directions. This viewpoint immediately
    explains uniqueness of the apex up to isomorphism: reuse uniqueness of
    terminal objects, then forget the cones. This is how [limit_unique] is
    proved in the library. *)

(** ** 4. 终对象视角

    将 [D] 上的全部锥放入范畴 [ConeCat D]，其态射是与锥腿交换的顶点映射。
    每个锥都有唯一映射到极限锥，恰好就是说极限锥是这个范畴的终对象。

    [limit_iff_terminal] 证明双向对应。这也解释了为什么极限顶点在同构意义下
    唯一：复用终对象的唯一性，再忘却锥结构。本库的 [limit_unique] 正是这样证明的。 *)

Check @limit_iff_terminal.
Check @limit_unique.

(** ** 5. The adjunction view

    Suppose we have chosen limits for every diagram of shape [J]. The diagonal
    functor [Δ[J,C]] sends an object to its constant diagram. The limit functor
    [LimitF] sends a diagram to its selected limit. The universal property is
    then the hom-setoid correspondence

<<
       Hom(ΔX, D)  ≅  Hom(X, lim D).
>>

    A cone goes to its mediator; an arrow goes to the cone obtained by
    precomposing [πlim[D]]. Beta and eta make these maps inverse. Compatibility
    with precomposition and diagram transformations gives naturality.
    [LimitAdjunction] packages precisely these data as [Δ[J,C] ⊣ LimitF].

    Conversely a right adjoint to the diagonal supplies limiting cones by its
    counit. [limits_iff_diagonal_right_adjoint] states the complete two-way
    construction, retaining the chosen structures in both directions. *)

(** ** 5. 伴随视角

    假定为每个 [J] 形状的图式选定极限。对角函子 [Δ[J,C]] 将对象送到常图式，
    极限函子 [LimitF] 将图式送到选定极限。泛性质于是成为 Hom 广集的对应：

<<
       Hom(ΔX, D)  ≅  Hom(X, lim D).
>>

    锥被送到中介；箭头被送到与 [πlim[D]] 预合成得到的锥。β 和 η 保证两者互逆，
    与预合成及图式自然变换的相容性给出自然性。[LimitAdjunction] 将这些数据组织
    为 [Δ[J,C] ⊣ LimitF]。

    反过来，对角函子的右伴随通过余单位给出极限锥。
    [limits_iff_diagonal_right_adjoint] 陈述完整双向构造，并保留两个方向的选定结构。 *)

Check @limit_lift_resp.
Check @limit_cone_resp.
Check @LimitAdjunction.
Check @limits_iff_diagonal_right_adjoint.

(** A map of diagrams [α : D ⇒ E] respects every shape arrow [a : Hom i j].
    The naturality square explains the diagram-transformation side of the
    adjunction's naturality. Its equation is [nt_naturality α a]. *)

(** 图式映射 [α : D ⇒ E] 与每条形状箭头 [a : Hom i j] 相容。自然性方块解释
    伴随自然性中图式变换的一侧，其方程为 [nt_naturality α a]。 *)

(** @lang both
%
\[
\begin{tikzcd}[column sep=large, row sep=large]
  D(i) \arrow[r, "D(a)"] \arrow[d, "\alpha_i"']
    & D(j) \arrow[d, "\alpha_j"] \\
  E(i) \arrow[r, "E(a)"'] & E(j)
\end{tikzcd}
\]
%
*)

Check @nt_naturality.

(** ** 6. Pullbacks as a concrete shape

    A cospan [f : Hom A Z], [g : Hom B Z] gives a familiar instance of the
    same universal property. In the diagram below, [P] is its pullback.
    If [f ∘ u ≈ g ∘ v], the dashed mediator is unique with
    [p₁ ∘ h ≈ u] and [p₂ ∘ h ≈ v]. The equations again use specified equality.

    [pullback_iff_limit] identifies this property with being a limit of the
    cospan diagram. The library's [pb] and [pullback_mediator_unique] provide
    the mediator and its two projection equations together with uniqueness. *)

(** ** 6. 拉回作为具体形状

    余跨度 [f : Hom A Z]、[g : Hom B Z] 给出同一泛性质的熟悉实例。下图中 [P]
    是其拉回。若 [f ∘ u ≈ g ∘ v]，则虚线中介在满足 [p₁ ∘ h ≈ u] 和
    [p₂ ∘ h ≈ v] 的箭头中唯一，方程仍使用指定相等。

    [pullback_iff_limit] 将此性质等同于余跨度图式的极限性质。库中的 [pb] 和
    [pullback_mediator_unique] 给出中介、两个投影方程及唯一性。 *)

(** @lang both
%
\[
\begin{tikzcd}[column sep=large, row sep=large]
  Q \arrow[drr, bend left=15, "v"]
    \arrow[ddr, bend right=15, "u"']
    \arrow[dr, dashed, "h" description] & & \\
  & P \arrow[r, "p_2"] \arrow[d, "p_1"'] & B \arrow[d, "g"] \\
  & A \arrow[r, "f"'] & Z
\end{tikzcd}
\]
%
*)

Check @pullback_iff_limit.
Check @pullback_mediator_unique.

(** ** What to try next

    Specialize the shape to two discrete objects and identify the two cone
    legs with product projections. Derive their projection equations from
    [limit_β], reusing the same mediator interface. *)

(** ** 接下来可以尝试什么

    将形状特化为两个离散对象，把两条锥腿识别为积投影，并从 [limit_β] 导出
    投影方程，复用同一套中介接口。 *)
