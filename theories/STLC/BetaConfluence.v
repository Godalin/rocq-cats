From Cats.STLC Require Export
  ContextConfluence
  ReductionRoot
  ReductionSubstitution
  StrongNormalization.
From Cats.Set.Relation Require Export Newman.

(** * Confluence of Full Beta Contraction

    Root beta peaks are resolved directly. A root contraction commutes
    with reduction in a retained component; reduction in a discarded
    component disappears. For function beta, substitution preserves a
    body step, while an argument step may have several residual copies.
    The existing substitution-path theorem accounts for all occurrences.

    The rule-independent context theorem then gives local confluence,
    and Newman's lemma combines it with strong normalization. The result
    covers all intrinsically typed terms and full reduction under binders.
    No equality decision on base labels is required. *)

(** * 完整 β 收缩的合流

    直接解决根 β 分叉。根收缩与保留分量中的归约交换；被丢弃分量中的归约
    则消失。对于函数 β，替换保持项体步骤，而实参步骤可能留下多个副本。
    既有替换路径定理处理全部出现位置。

    随后由独立于规则的上下文定理得到局部合流，再用 Newman 引理及强归一化
    得到合流。结论覆盖全部内在类型化项及绑定之下的完整归约，不要求基类型
    标签的相等可判定。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Root Peaks and Their Contexts

    Fix arbitrary base labels and independent step, path and auxiliary
    classification bounds. Source-indexed views identify the changed
    child without a dependent constructor-injection principle. *)

(** ** 根分叉及其上下文

    固定任意基类型标签，以及独立的步骤界、路径界和辅助分类界。以来源为索引
    的视图识别改变的子项，不需要依赖构造器的单射原则。 *)

Section BetaConfluence.
Universes b e p l.
Constraint b <= e, e < l.
Context {B : Type@{b}}.

(** Every root beta contraction joins every other beta step from its
    source. In the argument case, the left leg is a path rather than a
    single step because substitution can duplicate or discard the step. *)

(** 任意根 β 收缩都可与同源的任意 β 步骤汇合。在实参分支中，左腿是一条
    路径而非单步，因为替换可能复制或丢弃该步骤。 *)

Definition beta_root_join {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}
    (h : RootBeta@{b e b} t u) (k : BetaStep@{b e l b} t v)
  : Join@{b e p} BetaStep@{b e l b} u v.
Proof.
  destruct h as [Γ A U body arg | Γ A U first second |
    Γ A U first second].
  - destruct (beta_step_app_inv k) as [r | [[f [s z]] | [a [s z]]]].
    + pose proof (root_beta_unique (root_beta_function body arg) r) as z.
      subst v. exact (join_refl _).
    + destruct (beta_step_lam_inv s) as [body' [s' z']].
      subst f v. exists (body'[arg/]). split.
      * exact (rtc_step (beta_step_subst s' Γ (sub_single arg))).
      * exact (rtc_step (context_step_root _
          (root_beta_function body' arg))).
    + subst v. exists (body[a/]). split.
      * exact (beta_rtc_single body (rtc_step s)).
      * exact (rtc_step (context_step_root _
          (root_beta_function body a))).
  - destruct (beta_step_fst_inv k) as [r | [pair' [s z]]].
    + pose proof (root_beta_unique (root_beta_fst first second) r) as z.
      subst v. exact (join_refl _).
    + destruct (beta_step_pair_inv s) as
        [[first' [s' z']] | [second' [s' z']]]; subst pair' v.
      * exists first'. split.
        -- exact (rtc_step s').
        -- exact (rtc_step (context_step_root _
            (root_beta_fst first' second))).
      * exists first. split.
        -- exact (rtc_refl _).
        -- exact (rtc_step (context_step_root _
            (root_beta_fst first second'))).
  - destruct (beta_step_snd_inv k) as [r | [pair' [s z]]].
    + pose proof (root_beta_unique (root_beta_snd first second) r) as z.
      subst v. exact (join_refl _).
    + destruct (beta_step_pair_inv s) as
        [[first' [s' z']] | [second' [s' z']]]; subst pair' v.
      * exists second. split.
        -- exact (rtc_refl _).
        -- exact (rtc_step (context_step_root _
            (root_beta_snd first' second))).
      * exists second'. split.
        -- exact (rtc_step s').
        -- exact (rtc_step (context_step_root _
            (root_beta_snd first second'))).
Defined.

(** The generic constructor argument lifts the root diagrams to every
    one-step peak, including overlapping contexts and disjoint children. *)

(** 一般构造器论证将根图式提升到任意单步分叉，包括重叠上下文与不同子项。 *)

Definition beta_locally_confluent (Γ : Ctx B) (A : Ty B)
  : is_locally_confluent@{b e p _} (@BetaStep@{b e l b} B Γ A)
  := context_locally_confluent (@RootBeta@{b e b} B)
      (λ Γ A t u v h k, beta_root_join h k) Γ A.

(** Strong normalization supplies the well-founded recursion required by
    Newman; the output records both finite joining paths. *)

(** 强归一化提供 Newman 所需的良基递归；输出记录两条有限汇合路径。 *)

Definition beta_confluent (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaStep@{b e l b} B Γ A)
  := newman (beta_locally_confluent Γ A)
      (λ t, beta_strong_normalization t).

(** Two irreducible beta results of one term are the same typed syntax
    tree. Existence of such a result is a separate computational question. *)

(** 同一项的两个 β 不可约结果是同一带类型语法树。此类结果的存在性是另一个
    计算问题。 *)

Definition beta_irreducible_unique {Γ : Ctx B} {A : Ty B}
    {t u v : Tm Γ A}
    (p : ReflTransClosure@{b e p} BetaStep@{b e l b} t u)
    (q : ReflTransClosure@{b e p} BetaStep@{b e l b} t v)
    (hu : is_irreducible BetaStep@{b e l b} u)
    (hv : is_irreducible BetaStep@{b e l b} v)
  : u = v
  := confluent_irreducible_unique (beta_confluent Γ A t) p q hu hv.

End BetaConfluence.
