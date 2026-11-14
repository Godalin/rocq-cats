From Cats.STLC Require Export ReductionSubstitution.
From Cats.Set.Relation Require Import
  Compatible
  Sum.

(** * Function and Product Eta Contraction

    Reverse the existing eta-expansion rules and their contextual closure.
    This retains one underlying construction. Function freshness is
    encoded by weakening into a fresh binder, without a decision procedure
    for free variables. Product contraction removes duplicated projections.

    Combine beta and eta contraction by the existing relation coproduct.
    Unit equations are not reduction rules here. Soundness into [TmEq]
    remains available, but this does not assert that the smaller rule set
    generates its unit equations. Combined normalization and confluence
    require separate interaction arguments. *)

(** * 函数与积的 η 收缩

    反转既有 η 展开规则及其上下文闭包，保留一个底层构造。函数的新鲜性由向
    新绑定下的弱化编码，无须判定自由变量。积收缩去掉重复的投影。

    用既有关系余积组合 β 与 η 收缩。单位方程在这里不是归约规则；仍可证明
    到 [TmEq] 的可靠性，但不声称这个较小规则集生成其中的单位方程。组合关系
    的归一化与合流需要另外证明其相互作用。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** Eta contraction is the original root relation with reversed endpoints. *)

(** η 收缩是反转端点后的原根关系。 *)

Definition RootEtaContract@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type@{e}
  := RootEtaExpand@{b e b} u t.

(** The variable bound by the lambda is fresh for the weakened function. *)

(** λ 绑定的变量对弱化后的函数是新鲜变量。 *)

Definition root_eta_contract_function@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A U : Ty B} (f : Tm Γ (A ⇒ U))
  : RootEtaContract@{b e} (ƛ (f⟨wkRen⟩ · (# var_zero))) f
  := root_eta_function f.

(** Contract the two projections of one and the same product term. *)

(** 收缩同一个积项的两个投影。 *)

Definition root_eta_contract_product@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A U : Ty B} (p : Tm Γ (A × U))
  : RootEtaContract@{b e} (⟨π₁ p, π₂ p⟩) p
  := root_eta_product p.

(** Contextual contraction reverses contextual expansion, also under
    binders and in either component of a binary constructor. *)

(** 上下文收缩反转上下文展开，包括绑定下和二元构造器的任一分量内。 *)

Definition EtaContractStep@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A t u, @EtaExpandStep@{b e _ b} B Γ A u t.

Arguments EtaContractStep {_ _ _} _ _.

(** Embed a reversed root generator in its empty context. *)

(** 将反向根生成元嵌入空上下文。 *)

Definition eta_contract_root@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaContract@{b e} t u)
  : EtaContractStep@{b e _} t u
  := context_step_root (@RootEtaExpand@{b e b} B) h.

(** Each one-hole operation preserves contraction. *)

(** 每个单孔操作都保持收缩。 *)

Definition eta_contract_lift@{b e +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A U : Ty B} (c : TmOperation (Γ, A) (Δ, U))
    {t u : Tm Γ A} (h : EtaContractStep@{b e _} t u)
  : EtaContractStep@{b e _} (TmContexts B _ _ c t)
      (TmContexts B _ _ c u)
  := context_step_lift (@RootEtaExpand@{b e b} B) c h.

(** The generic reversal fold presents the same edge using contexts over
    reversed generators. No second chosen closure is introduced. *)

(** 一般反向折叠用反向生成元上的上下文呈现同一条边，不引入第二个选定闭包。 *)

Definition eta_contract_context@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : EtaContractStep@{b e _} t u)
  : ContextStep (@RootEtaContract@{b e} B) t u
  := context_closure_reverse (TmContexts B)
      (tm_relation_family (@RootEtaExpand@{b e b} B)) h.

(** Reversing the reversed generators recovers the original expansion. *)

(** 再次反转已反向的生成元，恢复原展开。 *)

Definition context_eta_contract@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ContextStep (@RootEtaContract@{b e} B) t u)
  : EtaContractStep@{b e _} t u
  := context_closure_reverse (TmContexts B)
      (tm_relation_family (@RootEtaContract@{b e} B)) h.

(** Beta and eta are tagged alternatives, not consecutive steps. *)

(** β 与 η 是带标签的备选，而不是连续步骤。 *)

Definition BetaEtaContractStep@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, @BetaStep@{b e _ b} B Γ A ⊕R
      @EtaContractStep@{b e _} B Γ A.

Arguments BetaEtaContractStep {_ _ _} _ _.

(** Every surrounding constructor preserves either tagged alternative. *)

(** 每个外层构造器都保持任一带标签备选。 *)

Definition beta_eta_contract_lift@{b e +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A U : Ty B} (c : TmOperation (Γ, A) (Δ, U))
    {t u : Tm Γ A} (h : BetaEtaContractStep@{b e _} t u)
  : BetaEtaContractStep@{b e _} (TmContexts B _ _ c t)
      (TmContexts B _ _ c u).
Proof.
  destruct h as [h | h].
  - exact (inl (beta_step_lift c h)).
  - exact (inr (eta_contract_lift c h)).
Defined.

(** Substitution preserves expansion: old variables are weakened beneath
    the binder while the fresh variable remains fixed. *)

(** 替换保持展开：旧变量在绑定下弱化，而新鲜变量保持不变。 *)

Definition root_eta_expand_subst@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaExpand@{b e b} t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : RootEtaExpand@{b e b} t[σ] u[σ].
Proof.
  destruct h; cbn.
  - rewrite subst_weaken. exact (root_eta_function f[σ]).
  - exact (root_eta_product p[σ]).
Defined.

(** Root contraction uses the same transformation with swapped endpoints. *)

(** 根收缩在交换端点后使用同一个转换。 *)

Definition root_eta_contract_subst@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaContract@{b e} t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : RootEtaContract@{b e} t[σ] u[σ]
  := root_eta_expand_subst h Δ σ.

(** The general substituted-generator fold handles all enclosing contexts. *)

(** 一般替换生成元折叠处理全部外层上下文。 *)

Definition eta_contract_subst@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : EtaContractStep@{b e _} t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : EtaContractStep@{b e _} t[σ] u[σ]
  := context_step_subst (@RootEtaExpand@{b e b} B)
      (@RootEtaExpand@{b e b} B)
      (λ Γ A t u h Δ σ,
        context_step_root _ (root_eta_expand_subst h Δ σ)) h Δ σ.

(** Renaming is substitution by variables, so it needs no separate
    argument about freshness. *)

(** 重命名是用变量作替换，因而无须另作新鲜性论证。 *)

Definition eta_contract_rename@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : EtaContractStep@{b e _} t u) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : EtaContractStep@{b e _} t⟨ρ⟩ u⟨ρ⟩.
Proof.
  rewrite <- !subst_ren. exact (eta_contract_subst h Δ (RenSub ρ)).
Defined.

(** Substitution preserves the selected coproduct branch. *)

(** 替换保持所选的余积分支。 *)

Definition beta_eta_contract_subst@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e _} t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : BetaEtaContractStep@{b e _} t[σ] u[σ].
Proof.
  destruct h as [h | h].
  - exact (inl (beta_step_subst h Δ σ)).
  - exact (inr (eta_contract_subst h Δ σ)).
Defined.

(** Reindexing likewise preserves either alternative. *)

(** 重索引同样保持任一备选分支。 *)

Definition beta_eta_contract_rename@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e _} t u) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : BetaEtaContractStep@{b e _} t⟨ρ⟩ u⟨ρ⟩.
Proof.
  destruct h as [h | h].
  - exact (inl (beta_step_rename h Δ ρ)).
  - exact (inr (eta_contract_rename h Δ ρ)).
Defined.

(** Reverse the already proved equation for an expansion edge. Explicit
    fold targets keep syntax and edge-evidence sizes independent. *)

(** 反转展开边已经证明的等式。显式折叠目标保持语法与边证据大小独立。 *)

Definition eta_contract_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : EtaContractStep@{b e _} t u)
  : TmEq@{b e b} t u
  := tm_eq_sym (context_closure_preserves (TmContexts B)
      (S := tm_relation_family (@TmEq@{b e b} B))
      tm_eq_compatible
      (λ i, @root_eta_to_tm_eq@{b e b} B (fst i) (snd i))
      (Γ, A) u t h).

(** Copair the two equation interpreters. This supplies soundness only;
    the unit equation remains outside the contraction relation. *)

(** 对两个等式解释作余配对。这只给出可靠性；单位方程仍在收缩关系之外。 *)

Definition beta_eta_contract_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e _} t u)
  : TmEq@{b e b} t u.
Proof.
  destruct h as [h | h].
  - exact (context_closure_preserves (TmContexts B)
      (S := tm_relation_family (@TmEq@{b e b} B))
      tm_eq_compatible
      (λ i, @root_beta_to_tm_eq@{b e b} B (fst i) (snd i))
      (Γ, A) t u h).
  - exact (eta_contract_to_tm_eq h).
Defined.
