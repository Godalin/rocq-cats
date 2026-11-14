From Cats.STLC Require Export
  BetaEtaPaths
  BetaConfluence
  EtaSource
  ReductionRenaming.

(** * Mixed Local Beta/Eta Peaks

    Strong normalization used a sequential eta-then-beta diagram. Local
    confluence instead asks about two steps with a shared source. Here
    root beta is joined with contextual eta, and root eta with contextual
    beta. A rule-independent context theorem lifts both diagrams to all
    mixed peaks. Eta/eta peaks require a separate argument.
    Root beta and root eta cannot coincide, but their redexes can overlap
    through an immediate introduction or through substitution. *)

(** * 混合的局部 βη 分叉

    强归一化使用先 η 后 β 的连续图式；局部合流则处理来源相同的两个步骤。
    这里将根 β 与上下文 η 汇合，也将根 η 与上下文 β 汇合，再由独立于规则的
    上下文定理提升到全部混合分叉。η／η 分叉需另行论证。根 β 与根 η 不会
    重合，但其可归约式可以通过直接引入形式或替换发生重叠。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Mixed Root Diagrams

    Fix arbitrary labels and independent syntax, edge, path and auxiliary
    classification bounds. Eta source observations keep the introduction
    types aligned; argument changes use mixed substitution paths. *)

(** ** 混合根图式

    固定任意标签，以及独立的语法、边、路径和辅助分类界。η 来源观测保持引入
    类型一致；实参变化使用混合替换路径。 *)

Section BetaEtaLocal.
Universes b e p l.
Constraint b <= e, e < l.
Context {B : Type@{b}}.

(** A root beta step and an eta step from the same source join. When eta
    contracts the immediately enclosing introduction, both endpoints
    already agree; otherwise the appropriate residual is retained. *)

(** 同源的根 β 步骤与 η 步骤可汇合。若 η 收缩紧邻的引入形式，则两个终点
    已经相等；否则保留相应剩余步骤。 *)

Definition beta_root_eta_join {Γ : Ctx B} {A : Ty B}
    {t u v : Tm Γ A} (h : RootBeta@{b e b} t u)
    (k : EtaContractStep@{b e l} t v)
  : Join@{b e p} BetaEtaContractStep@{b e l} u v.
Proof.
  pose proof (eta_contract_source k) as source.
  destruct source as [r | child].
  { exact (match root_eta_neutral_absurd r (root_beta_neutral h) with end). }
  clear k. destruct h as [Γ A U body arg | Γ A U first second |
    Γ A U first second]; cbn in child.
  - destruct child as [[f [s z]] | [a [s z]]].
    + destruct (context_step_source _ s) as [r | [body' [s' z']]].
      * pose proof (root_eta_source r) as shape. cbn in shape.
        injection shape as shape. subst body v. cbn.
        rewrite subst_weaken_single. exact (join_refl _).
      * subst f v. exists (body'[arg/]). split.
        -- exact (rtc_step (inr (eta_contract_subst
            (context_eta_contract s') Γ (sub_single arg)))).
        -- exact (rtc_step (inl (context_step_root _
            (root_beta_function body' arg)))).
    + subst v. exists (body[a/]). split.
      * exact (beta_eta_rtc_single body
          (rtc_step (inr (context_eta_contract s)))).
      * exact (rtc_step (inl (context_step_root _
          (root_beta_function body a)))).
  - destruct child as [pair' [s z]].
    destruct (context_step_source _ s) as [r | children].
    + pose proof (root_eta_source r) as shape. cbn in shape.
      injection shape as left right. subst first second v.
      exact (join_refl _).
    + destruct children as [[first' [s' z']] | [second' [s' z']]];
        subst pair' v.
      * exists first'. split.
        -- exact (rtc_step (inr (context_eta_contract s'))).
        -- exact (rtc_step (inl (context_step_root _
            (root_beta_fst first' second)))).
      * exists first. split.
        -- exact (rtc_refl _).
        -- exact (rtc_step (inl (context_step_root _
            (root_beta_fst first second')))).
  - destruct child as [pair' [s z]].
    destruct (context_step_source _ s) as [r | children].
    + pose proof (root_eta_source r) as shape. cbn in shape.
      injection shape as left right. subst first second v.
      exact (join_refl _).
    + destruct children as [[first' [s' z']] | [second' [s' z']]];
        subst pair' v.
      * exists second. split.
        -- exact (rtc_refl _).
        -- exact (rtc_step (inl (context_step_root _
            (root_beta_snd first' second)))).
      * exists second'. split.
        -- exact (rtc_step (inr (context_eta_contract s'))).
        -- exact (rtc_step (inl (context_step_root _
            (root_beta_snd first second')))).
Defined.

(** Conversely put eta at the root. A beta step inside its duplicated
    product is copied to the other projection before eta is contracted.
    In a function, reflection through weakening reconstructs the step in
    the original function. Beta at the fresh application returns an
    already present lambda body by the binder substitution equation. *)

(** 反过来将 η 放在根部。积的一个副本内的 β 步骤被复制到另一个投影，再
    收缩 η。函数情形通过弱化反射重构原函数中的步骤；新鲜应用处的 β 则由
    绑定替换等式恢复已经存在的 λ 项体。 *)

Definition eta_root_beta_join {Γ : Ctx B} {A : Ty B}
    {t u v : Tm Γ A} (h : RootEtaContract@{b e} t u)
    (k : BetaStep@{b e l b} t v)
  : Join@{b e p} BetaEtaContractStep@{b e l} u v.
Proof.
  destruct h as [Γ A U f | Γ A U pair].
  - destruct (beta_step_lam_inv k) as [body' [s z]].
    destruct (beta_step_app_inv s) as [r | [[f' [s' z']] | [a' [s' z']]]].
    + pose proof (root_beta_contractum r) as target. cbn in target.
      rewrite (lambda_body_rename f _ wkRen) in target.
      pose proof (lambda_body_spec f) as shape.
      destruct (lambda_body f) as [body |] eqn:parts;
        cbn in *; rewrite ?parts in target, shape; cbn in *;
        [| discriminate target].
      injection target as target. subst body' v.
      rewrite rename_lift_single, shape. exact (join_refl _).
    + destruct (beta_step_rename_inv f _ wkRen f' s') as [g [s'' shape]].
      subst f' body' v. exists g. split.
      * exact (rtc_step (inl s'')).
      * exact (rtc_step (inr (eta_contract_root
          (root_eta_contract_function g)))).
    + exact (match beta_step_var_absurd _ s' with end).
  - destruct (beta_step_pair_inv k) as
      [[first' [s z]] | [second' [s z]]].
    + destruct (beta_step_fst_inv s) as [r | [pair' [s' z']]].
      * pose proof (root_beta_contractum r) as target. cbn in target.
        pose proof (pair_parts_spec pair) as shape.
        destruct (pair_parts pair) as [[first second] |] eqn:parts;
          cbn in *; rewrite ?parts in target, shape; cbn in *;
          [| discriminate target].
        injection target as target. subst first' v. rewrite shape.
        exists (⟨first, second⟩). split.
        -- exact (rtc_refl _).
        -- exact (rtc_step (inl (beta_step_lift (op_pair_r first)
            (context_step_root _ (root_beta_snd first second))))).
      * subst first' v. exists pair'. split.
        -- exact (rtc_step (inl s')).
        -- exact (rtc_cons (inl (beta_step_lift (op_pair_r (π₁ pair'))
            (beta_step_lift op_snd s')))
            (rtc_step (inr (eta_contract_root
              (root_eta_contract_product pair'))))).
    + destruct (beta_step_snd_inv s) as [r | [pair' [s' z']]].
      * pose proof (root_beta_contractum r) as target. cbn in target.
        pose proof (pair_parts_spec pair) as shape.
        destruct (pair_parts pair) as [[first second] |] eqn:parts;
          cbn in *; rewrite ?parts in target, shape; cbn in *;
          [| discriminate target].
        injection target as target. subst second' v. rewrite shape.
        exists (⟨first, second⟩). split.
        -- exact (rtc_refl _).
        -- exact (rtc_step (inl (beta_step_lift (op_pair_l second)
            (context_step_root _ (root_beta_fst first second))))).
      * subst second' v. exists pair'. split.
        -- exact (rtc_step (inl s')).
        -- exact (rtc_cons (inl (beta_step_lift (op_pair_l (π₂ pair'))
            (beta_step_lift op_fst s')))
            (rtc_step (inr (eta_contract_root
              (root_eta_contract_product pair'))))).
Defined.

(** The reusable two-family context theorem lifts both root diagrams to
    arbitrary beta/eta peaks. Its common target is the tagged mixed
    relation, so this theorem asserts mixed local joinability. It leaves
    eta/eta peaks to a separate argument. *)

(** 可复用的双规则族上下文定理将两个根图式提升到任意 βη 分叉。共同目标为
    带标签混合关系，因此此定理断言混合局部可汇合性；η／η 分叉另行处理。 *)

Definition beta_eta_locally_joinable (Γ : Ctx B) (A : Ty B)
  : is_locally_joinable@{b e e e p _}
      (@BetaStep@{b e l b} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A).
Proof.
  intros t u v h k.
  exact (context_locally_joinable (@RootBeta@{b e b} B)
    (@RootEtaContract@{b e} B) (@BetaEtaContractStep@{b e l} B)
    beta_eta_contract_compatible
    (λ Γ A x y h, inl h)
    (λ Γ A x y h, inr (context_eta_contract h))
    (λ Γ A x y z h k, beta_root_eta_join h (context_eta_contract k))
    (λ Γ A x y z h k, join_sym (eta_root_beta_join h k))
    Γ A t u v h (eta_contract_context k)).
Defined.

End BetaEtaLocal.
