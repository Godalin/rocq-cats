From Cats.STLC Require Export
  EtaLocal
  HeadNormalization.

(** * Synchronizing Product Projections along Head Beta Paths

    Equal raw projections need not be cancelled by dependent constructor
    injection. Instead their head computations synchronize: every selected
    step on one product target induces a selected step on the other, with
    equal projections again. Thus a target that reaches a pair or variable
    has an unconditional beta join with its competing eta target.

    The general reduction below leaves an explicit obligation for blocked
    elimination heads. It does not construct full beta/eta confluence. *)

(** * 沿头部 β 路径同步积投影

    相等的原始投影不必通过依赖构造器单射来消去。可以同步其头部计算：一个
    积目标的每个选定步骤都在另一目标上诱导一个选定步骤，之后两个投影仍然
    分别相等。因此，到达配对或变量的目标与其竞争 η 目标无条件按 β 汇合。

    以下一般约化仍为被阻塞的消去头保留显式义务，不构造完整 βη 合流。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** A Synchronized Selected Step

    Fix arbitrary labels. Pair observations distinguish a root projection
    redex from a lifted child step, without comparing hidden type indices. *)

(** ** 同步选定步骤

    固定任意标签。配对观测区分投影根可归约式和提升的子项步骤，无须比较
    隐藏的类型索引。 *)

Section ProjectionSteps.
Context {B : Type}.

(** A reducible head cannot already be a pair introduction. *)

(** 可归约的头部不可能已经是配对引入。 *)

Definition head_contractum_nonpair {Γ : Ctx B} {A U : Ty B}
    (t u : Tm Γ (A × U)) (step : head_contractum t = Some u)
  : pair_parts t = None.
Proof.
  pose proof (pair_parts_spec t) as spec.
  destruct (pair_parts t) as [[a v] |]; [| reflexivity].
  cbn in spec. subst t. discriminate step.
Defined.

(** Both projections select the same residual child. One projection
    discovers its existence; the other preserves the second component. *)

(** 两个投影选定同一剩余子项。一个投影发现其存在，另一个保持第二分量。 *)

Definition product_projection_head_step {Γ : Ctx B} {A U : Ty B}
    (t u v : Tm Γ (A × U)) (step : HeadBetaStep t u)
    (left : π₁ t = π₁ v) (right : π₂ t = π₂ v)
  : ∃ w, HeadBetaStep v w ∧ (π₁ u = π₁ w) ∧ (π₂ u = π₂ w).
Proof.
  pose proof (head_beta_observation _ _ step) as observed.
  pose proof (head_contractum_nonpair t u observed) as parts.
  pose proof (product_projection_parts t v left right) as same_parts.
  pose proof (f_equal head_contractum left) as first.
  pose proof (f_equal head_contractum right) as second.
  rewrite (head_contractum_fst t parts),
    (head_contractum_fst v (eq_trans (eq_sym same_parts) parts)),
    observed in first.
  rewrite (head_contractum_snd t parts),
    (head_contractum_snd v (eq_trans (eq_sym same_parts) parts)),
    observed in second.
  destruct (head_contractum v) as [w |] eqn:next;
    cbn in first, second; [| discriminate first].
  exists w. split; [exact {|head_beta_observation := next|} |].
  split.
  - exact (f_equal (λ z, match z with
      | Some q => q | None => π₁ u end) first).
  - exact (f_equal (λ z, match z with
      | Some q => q | None => π₂ u end) second).
Defined.

(** Head termination also agrees between non-pair targets with equal
    projections. Thus the final residual problem has two blocked heads. *)

(** 投影分别相等的非配对目标也同时头部终止。因此最终剩余问题的两个头部
    都被阻塞。 *)

Definition product_projection_head_terminal {Γ : Ctx B} {A U : Ty B}
    (t v : Tm Γ (A × U)) (parts : pair_parts t = None)
    (left : π₁ t = π₁ v) (right : π₂ t = π₂ v)
    (terminal : head_contractum t = None)
  : head_contractum v = None.
Proof.
  pose proof (product_projection_parts t v left right) as same_parts.
  pose proof (f_equal head_contractum left) as first.
  rewrite (head_contractum_fst t parts),
    (head_contractum_fst v (eq_trans (eq_sym same_parts) parts)),
    terminal in first.
  destruct (head_contractum v); [discriminate first | reflexivity].
Defined.

End ProjectionSteps.

(** ** Finite Paths and Root Joins

    Keep beta/eta edge and finite-path bounds separate from the auxiliary
    classification bound. The synchronization itself uses small selected
    edges; mapping to beta retains full contextual witnesses. *)

(** ** 有限路径与根汇合

    βη 边界与有限路径界独立于辅助分类界。同步本身使用小型选定边；映为 β
    时仍保留完整上下文见证。 *)

Section ProjectionPaths.
Universes b e p l.
Constraint b <= e, e <= p, e < l.
Context {B : Type@{b}}.

(** Synchronize a whole strategy path, retaining the opposite path and
    the two endpoint equations. No confluence theorem is used. *)

(** 同步整条策略路径，保留对侧路径及端点的两个等式，不使用合流定理。 *)

Definition product_projection_head_path {Γ : Ctx B} {A U : Ty B}
    {t u : Tm Γ (A × U)}
    (path : ReflTransClosure@{b Set p} HeadBetaStep t u)
  : ∀ v, π₁ t = π₁ v → π₂ t = π₂ v →
      ∃ w, ReflTransClosure@{b Set p} HeadBetaStep v w ∧
        (π₁ u = π₁ w) ∧ (π₂ u = π₂ w).
Proof.
  induction path as [t | t x u step path ih]; intros v left right.
  - exists v. exact (rtc_refl v, (left, right)).
  - destruct (product_projection_head_step t x v step left right)
      as [w [next [first second]]].
    destruct (ih w first second) as [z [rest same]].
    exists z. exact (rtc_cons next rest, same).
Defined.

(** The two native projection equations reconstruct a competing root,
    at the same context and product type. *)

(** 两个原生投影等式在相同上下文和积类型处重构竞争根。 *)

Definition root_eta_of_product_projections {Γ : Ctx B} {A U : Ty B}
    (t v : Tm Γ (A × U)) (left : π₁ t = π₁ v) (right : π₂ t = π₂ v)
  : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v.
Proof. rewrite left, right. exact (root_eta_contract_product v). Defined.

(** A head path to a pair solves the original peak by beta paths alone.
    This includes elimination targets, not just displayed pair targets. *)

(** 到配对的头路径仅用 β 路径解决原分叉；这包括消去形式目标，而非只包括
    已显示为配对的目标。 *)

Definition eta_product_root_beta_join_of_head_pair
    {Γ : Ctx B} {A U : Ty B} (t v : Tm Γ (A × U))
    (a : Tm Γ A) (u : Tm Γ U)
    (path : ReflTransClosure@{b Set p} HeadBetaStep t (⟨a, u⟩))
    (root : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v)
  : Join@{b e p} BetaStep@{b e l b} t v.
Proof.
  destruct (root_eta_product_projections t v root) as [left right].
  destruct (product_projection_head_path path v left right)
    as [w [other [first second]]].
  pose proof (root_eta_product_pair_unique a u w
    (root_eta_of_product_projections (⟨a, u⟩) w first second)) as same.
  subst w. exists (⟨a, u⟩). split;
    exact (head_beta_path_beta path) || exact (head_beta_path_beta other).
Defined.

(** A path to a variable uses coherent marker recovery at its endpoint. *)

(** 到变量的路径在端点复用相干的标记恢复。 *)

Definition eta_product_root_beta_join_of_head_var
    {Γ : Ctx B} {A U : Ty B} (t v : Tm Γ (A × U))
    (x : Var Γ (A × U))
    (path : ReflTransClosure@{b Set p} HeadBetaStep t (# x))
    (root : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v)
  : Join@{b e p} BetaStep@{b e l b} t v.
Proof.
  destruct (root_eta_product_projections t v root) as [left right].
  destruct (product_projection_head_path path v left right)
    as [w [other [first second]]].
  pose proof (root_eta_product_var_unique x w
    (root_eta_of_product_projections (# x) w first second)) as same.
  subst w. exists (# x). split;
    exact (head_beta_path_beta path) || exact (head_beta_path_beta other).
Defined.

(** A join at the synchronized endpoints gives a join at the original
    targets by prefixing the two retained beta paths. *)

(** 在同步端点的汇合前接两条保留的 β 路径，即得到原目标的汇合。 *)

Definition eta_product_root_join_of_head_path
    {Γ : Ctx B} {A U : Ty B} {t u : Tm Γ (A × U)}
    (path : ReflTransClosure@{b Set p} HeadBetaStep t u)
    (v : Tm Γ (A × U))
    (root : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v)
    (endpoint : ∀ w, RootEtaContract@{b e} (⟨π₁ u, π₂ u⟩) w →
      Join@{b e p} BetaEtaContractStep@{b e l} u w)
  : Join@{b e p} BetaEtaContractStep@{b e l} t v.
Proof.
  destruct (root_eta_product_projections t v root) as [left right].
  destruct (product_projection_head_path path v left right)
    as [w [other [first second]]].
  exact (join_prefix
    (rtc_preserves (λ x, x)
      (λ x y k, rtc_step (inl k : BetaEtaContractStep@{b e l} x y))
      (head_beta_path_beta path))
    (rtc_preserves (λ x, x)
      (λ x y k, rtc_step (inl k : BetaEtaContractStep@{b e l} x y))
      (head_beta_path_beta other))
    (endpoint w (root_eta_of_product_projections u w first second))).
Defined.

End ProjectionPaths.

(** ** The Remaining Head-Normal Obligation

    Supply joins only at blocked elimination heads. Beta SN provides a
    finite head path for every target; pair and variable endpoints are
    solved without this input. The input itself is not constructed here. *)

(** ** 剩余的头正规义务

    只在被阻塞的消去头处提供汇合。β 强归一化为任意目标提供有限头路径；
    配对和变量端点的解决不使用此输入。本模块并未构造该输入。 *)

Section HeadNormalRoots.
Universes b e p l.
Constraint b <= e, e <= p, e < l.
Context {B : Type@{b}}.

(** An explicitly supplied diagram at head-terminal elimination targets;
    redexes may still occur in their arguments. *)

(** 在头部终止的消去形式目标处显式提供的图式；其实参中仍可有可归约式。 *)

Definition is_eta_head_elimination_root_joinable
  : Type@{p}
  := ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
      RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v →
      pair_parts t = None → variable_position t = None →
      head_contractum@{b b} t = None →
      Join@{b e p} BetaEtaContractStep@{b e l} t v.

Universe s.
Constraint e <= s.

(** Reduce the original product-root interface to the smaller explicit
    head-normal obligation. This remains a conditional construction. *)

(** 将原积根接口约化到更小的显式头正规义务；这仍然是条件式构造。 *)

Definition eta_product_roots_of_head_eliminations
    (remaining : is_eta_head_elimination_root_joinable)
  : @is_eta_product_root_joinable@{b e p l} B.
Proof.
  intros Γ A U t v root.
  pose proof (beta_strong_normalization t
    : SN@{b e s} BetaStep@{b e l b} t) as tree.
  destruct (head_normalize_sn t tree) as [u path terminal].
  apply (eta_product_root_join_of_head_path path v root).
  intros w k.
  pose proof (pair_parts_spec u) as pair_spec.
  destruct (pair_parts u) as [[a q] |] eqn:parts.
  - cbn in pair_spec. subst u.
    pose proof (root_eta_product_pair_unique a q w k) as same.
    subst w. exact (join_refl _).
  - pose proof (variable_position_spec u) as var_spec.
    destruct (variable_position u) as [x |] eqn:position.
    + cbn in var_spec. subst u.
      pose proof (root_eta_product_var_unique x w k) as same.
      subst w. exact (join_refl _).
    + exact (remaining Γ A U u w k parts position terminal).
Defined.

End HeadNormalRoots.
