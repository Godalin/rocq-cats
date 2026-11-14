From Cats.STLC Require Export
  ContextSource
  EtaContraction
  ReductionRoot.

(** * Reading the Source of Eta Contraction

    Reuse source analysis for arbitrary contextual rules, after presenting
    eta contraction as contexts over reversed generators. At the root,
    typed introduction observers expose the function body or product
    components. These observations avoid dependent constructor injection
    and make the overlaps with beta visible. *)

(** * 读取 η 收缩的来源

    将 η 收缩呈现为反向生成元上的上下文后，复用任意上下文规则的源分析。
    在根部，带类型的引入观测暴露函数项体或积分量。这些观测避免依赖构造器
    单射消去，使与 β 的重叠可供分析。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Root Observations

    Fix arbitrary base labels. The observation is indexed by the result
    type: only arrows and products admit a root eta contraction. *)

(** ** 根观测

    固定任意基类型标签。观测以结果类型为索引：只有箭头和积允许根 η 收缩。 *)

Section EtaRootObservations.
Context {B : Type}.

(** A function source exposes its weakened target applied to the fresh
    variable; a product source exposes both projections of its target. *)

(** 函数来源暴露弱化目标应用于新鲜变量的项体；积来源暴露目标的两个投影。 *)

Definition EtaRootSource {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type
  := match A as U return Tm Γ U → Tm Γ U → Type with
      | ty_arr U V => λ x y,
          lambda_body x = Some (y⟨wkRen⟩ · (# var_zero))
      | ty_prod U V => λ x y,
          pair_parts x = Some (π₁ y, π₂ y)
      | _ => λ _ _, Empty_set
      end t u.

End EtaRootObservations.

(** Each reversed root derivation supplies its source observation. The
    derivation is eliminated with its indices generalized. *)

(** 每个反向根推导提供其来源观测；消去该推导时泛化其索引。 *)

Definition root_eta_source@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaContract@{b e} t u)
  : EtaRootSource t u.
Proof. destruct h; reflexivity. Defined.

(** Root eta has an introduction source, so it cannot start at a raw
    neutral. In particular beta and eta have no common root redex. *)

(** 根 η 的来源为引入形式，故不能从原始中性项出发。特别地，β 与 η 没有
    共同的根可归约式。 *)

Definition root_eta_neutral_absurd@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaContract@{b e} t u)
  : is_neutral_tm t → Empty_set.
Proof. destruct h; exact (λ n, n). Defined.

(** The generic source view retains all root and immediate-child eta
    alternatives. Reversal does not change the location of the redex. *)

(** 一般来源视图保留全部根与直接子项 η 分支；反向不改变可归约式的位置。 *)

Definition eta_contract_source@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : EtaContractStep@{b e l} t u)
  : ContextSource (@RootEtaContract@{b e} B) t u
  := context_step_source _ (eta_contract_context h).

(** A variable has neither an introduction root nor an immediate child,
    so no eta contraction can start there. *)

(** 变量既没有引入形式的根，也没有直接子项，因此不能从变量作 η 收缩。 *)

Definition eta_contract_var_absurd@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (x : Var Γ A) {u : Tm Γ A}
    (h : EtaContractStep@{b e l} (# x) u)
  : Empty_set.
Proof.
  destruct (eta_contract_source h) as [h' | h'].
  - exact (root_eta_neutral_absurd h' tt).
  - exact h'.
Defined.

(** The unit constant has no eta contraction. The unit equation belongs
    to equational equality and is deliberately absent from this relation. *)

(** 单位常量没有 η 收缩。单位方程属于等式相等，此收缩关系特意未包含它。 *)

Definition eta_contract_unit_absurd@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {u : Tm Γ ⊤}
    (h : EtaContractStep@{b e l} ⋆ u)
  : Empty_set.
Proof.
  destruct (eta_contract_source h) as [h' | h'].
  - exact (root_eta_source h').
  - exact h'.
Defined.
