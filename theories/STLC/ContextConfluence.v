From Cats.STLC Require Export ContextSource.
From Cats.Set.Relation Require Export Confluence.
From Cats.Set.Relation Require Import Compatible.

(** * Local Peaks in Full Term Contexts

    Separate a root-rule problem from the structural context argument.
    Assume a root step can be joined with any contextual step from the
    same source, for either ordering of the two rule families. Their
    compatible closures then have joinable local peaks:
    reductions in the same child use induction, and reductions in distinct
    children commute. Abstraction is treated just like another one-hole
    operation, at its correctly extended typing context.

    This theorem is specific to the constructors of STLC, but independent
    of its reduction rules. It neither assumes termination nor supplies
    the root-overlap hypothesis for an arbitrary rule family. *)

(** * 完整项上下文中的局部分叉

    将根规则问题与上下文结构论证分开。假设两个规则族在两种次序下，同源的
    根步骤与上下文步骤均可汇合，则其相容闭包的局部分叉均可汇合：同一子项
    中的归约使用归纳，不同子项中的归约交换。抽象也作为单孔操作处理，其类型
    上下文正确扩张。

    此定理专属于 STLC 的构造器，但独立于具体归约规则。它既不假设终止性，
    也不为任意规则族自动提供根重叠假设。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Lifting Root Diagrams

    Fix two root rule families and a compatible target relation receiving
    their contextual steps, all at a common evidence bound. Supply joins
    for root/context peaks in both orders. Paths have a bound independent
    of both edge evidence and its classification bound.
    The paired induction target retains the first contextual step so that
    disjoint-child peaks can explicitly perform its residual step. *)

(** ** 提升根图式

    固定两个根规则族，以及接收其上下文步骤的相容目标关系，共用一个证据界。
    给出两种次序的根与上下文分叉汇合。路径界独立于边证据及其分类界。
    配对归纳目标保留第一个上下文步骤，使不同子项的分叉可显式执行其剩余步骤。 *)

Section ContextPeaks.
Universes b e p l.
Constraint b <= e, e < l.
Context {B : Type@{b}} (R : TmRelation@{b e l} B).
Context (S T : TmRelation@{b e l} B).
Context (compatible : is_compatible (TmContexts B) (tm_relation_family T)).
Context (includeR : ∀ Γ A, @ContextStep B R Γ A ⊆R T Γ A).
Context (includeS : ∀ Γ A, @ContextStep B S Γ A ⊆R T Γ A).
Context (rootR : ∀ Γ A (x y z : Tm Γ A), R Γ A x y →
  ContextStep S x z → Join@{b e p} (T Γ A) y z).
Context (rootS : ∀ Γ A (x y z : Tm Γ A), S Γ A x z →
  ContextStep R x y → Join@{b e p} (T Γ A) y z).

(** Enclosing constructors map a common reduct and both joining paths. *)

(** 外层构造器映射共同归约结果及两条汇合路径。 *)

Definition context_join_lift {Γ Δ : Ctx B} {A U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : Join@{b e p} (T Γ A) t u)
  : Join@{b e p} (T Δ U)
      (TmContexts B _ _ c t) (TmContexts B _ _ c u)
  := join_preserves (TmContexts B _ _ c)
      (λ x y k, compatible _ _ c x y k) h.

(** The recursive target resolves every second step. A second root step
    uses the supplied diagram in the reverse order. Otherwise source
    analysis identifies the same child or a disjoint child. *)

(** 递归目标处理任意第二步骤。若第二步在根部，则反向使用给定图式；否则源
    分析指出它位于同一子项还是不同子项。 *)

Definition context_join_compatible
  : is_compatible (TmContexts B)
      (λ i t u, ContextStep R t u ∧
        (∀ v, ContextStep S t v → Join@{b e p} (T _ _) u v)).
Proof.
  intros [Γ A] [Δ U] c t u [h ih]. split.
  - exact (context_step_lift R c h).
  - intros v k. destruct (context_step_source S k) as [root | child].
    + exact (rootS _ _ _ _ _ root (context_step_lift R c h)).
    + clear k. destruct c; cbn in child.
      * destruct child as [[w [k z]] | [w [k z]]]; subst v.
        -- exact (context_join_lift (op_pair_l u0) (ih w k)).
        -- exists (⟨u, w⟩). split.
           ++ exact (rtc_step (compatible _ _ (op_pair_r u) _ _
               (includeS _ _ _ _ k))).
           ++ exact (rtc_step (compatible _ _ (op_pair_l w) _ _
               (includeR _ _ _ _ h))).
      * destruct child as [[w [k z]] | [w [k z]]]; subst v.
        -- exists (⟨w, u⟩). split.
           ++ exact (rtc_step (compatible _ _ (op_pair_l u) _ _
               (includeS _ _ _ _ k))).
           ++ exact (rtc_step (compatible _ _ (op_pair_r w) _ _
               (includeR _ _ _ _ h))).
        -- exact (context_join_lift (op_pair_r t0) (ih w k)).
      * destruct child as [w [k z]]. subst v.
        exact (context_join_lift op_fst (ih w k)).
      * destruct child as [w [k z]]. subst v.
        exact (context_join_lift op_snd (ih w k)).
      * destruct child as [w [k z]]. subst v.
        exact (context_join_lift op_lam (ih w k)).
      * destruct child as [[w [k z]] | [w [k z]]]; subst v.
        -- exact (context_join_lift (op_app_l u0) (ih w k)).
        -- exists (u · w). split.
           ++ exact (rtc_step (compatible _ _ (op_app_r u) _ _
               (includeS _ _ _ _ k))).
           ++ exact (rtc_step (compatible _ _ (op_app_l w) _ _
               (includeR _ _ _ _ h))).
      * destruct child as [[w [k z]] | [w [k z]]]; subst v.
        -- exists (w · u). split.
           ++ exact (rtc_step (compatible _ _ (op_app_l u) _ _
               (includeS _ _ _ _ k))).
           ++ exact (rtc_step (compatible _ _ (op_app_r w) _ _
               (includeR _ _ _ _ h))).
        -- exact (context_join_lift (op_app_r t0) (ih w k)).
Defined.

(** Fold contextual derivations using the preceding structural argument.
    Only root/context diagrams remain a rule-specific obligation. *)

(** 用上述结构论证折叠上下文推导；只留下根与上下文图式这一规则特有的义务。 *)

Definition context_locally_joinable (Γ : Ctx B) (A : Ty B)
  : is_locally_joinable@{b e e e p _}
      (@ContextStep B R Γ A) (@ContextStep B S Γ A) (T Γ A).
Proof.
  intros t u v h k.
  exact (snd (context_closure_preserves (TmContexts B)
    context_join_compatible
    (λ i x y r,
      (context_step_root R r, λ z s, rootR _ _ x y z r s))
    (Γ, A) t u h) v k).
Defined.

End ContextPeaks.

(** Specialize both rule families and the target to one contextual
    relation. A single root-diagram hypothesis then gives local confluence. *)

(** 将两个规则族及目标专化为同一上下文关系；一个根图式假设即给出局部合流。 *)

Definition context_locally_confluent@{b e p l +} {B : Type@{b}}
    (R : TmRelation@{b e l} B)
    (root_join : ∀ Γ A (t u v : Tm Γ A), R Γ A t u →
      ContextStep R t v → Join@{b e p} (ContextStep R) u v)
    (Γ : Ctx B) (A : Ty B)
  : is_locally_confluent@{b e p _} (@ContextStep B R Γ A).
Proof.
  assert (compatible : is_compatible (TmContexts B)
    (tm_relation_family (λ Γ A, @ContextStep B R Γ A))).
  { intros [Δ U] [Θ V] c x y h. exact (context_step_lift R c h). }
  exact (context_locally_joinable R R (λ Γ A, @ContextStep B R Γ A)
    compatible
    (λ Γ A, relation_incl_id _) (λ Γ A, relation_incl_id _)
    root_join (λ Γ A x y z h k, join_sym (root_join Γ A x z y h k)) Γ A).
Defined.
