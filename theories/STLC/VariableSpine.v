From Cats.STLC Require Export
  EliminationSpine
  HeadReduction.

(** * Variable-Headed Raw Elimination Chains

    A context position determines the declared head type. From that type
    a forward spine determines every argument type, while a terminal
    binding marker retains the displayed result type. Extract this view
    from raw terms and embed it back without changing their syntax.

    The view allows arbitrary arguments, including beta redexes. It
    therefore covers blocked head-normal terms that are not eta-long
    neutrals. No equality decision on labels is used. *)

(** * 以变量为头部的原始消去链

    上下文位置确定声明的头部类型。由该类型出发，前向消去链确定每个实参
    类型，而终端绑定标记保留显示的结果类型。从原始项提取此视图，再嵌回时
    不改变语法。

    视图允许任意实参，包括 β 可归约式。因此它覆盖不属于 η 长中性项的
    阻塞头正规项。不使用标签相等判定。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Context Positions and Spines

    Keep the argument context [Γ] fixed while searching declarations in
    [Δ]. Older positions retain their sum tags; a newest position stores
    a spine at exactly its declared type. *)

(** ** 上下文位置与消去链

    保持实参上下文 [Γ] 固定，在 [Δ] 中搜索声明。旧位置保留和类型标签；
    最新位置存储精确位于其声明类型的消去链。 *)

Section VariableSpines.
Context {B : Type} (Γ : Ctx B).

(** A declaration position with a spine producing result type [A]. *)

(** 声明位置及产生结果类型 [A] 的消去链。 *)

Fixpoint VariableSpine (Δ : Ctx B) (A : Ty B)
  : Type
  := match Δ with
     | ctx_empty => Empty_set
     | ctx_snoc Θ D => VariableSpine Θ A + AlignedSpine Γ D A
     end.

(** A variable starts with an empty spine and its original marker. *)

(** 变量从空消去链及其原标记出发。 *)

Fixpoint variable_spine (Δ : Ctx B) (A : Ty B)
  : Var Δ A → VariableSpine Δ A.
Proof.
  destruct Δ as [| Δ D]; cbn; intros x;
    [exact (match x with end) |].
  destruct x as [x | x].
  - exact (inl (variable_spine Δ A x)).
  - exact (inr (inl x)).
Defined.

(** Embed through a supplied context map. All stored arguments already
    live in [Γ], so this map acts only on the head variable. *)

(** 沿给定上下文映射嵌入。所有存储实参已位于 [Γ]，映射仅作用于头部变量。 *)

Fixpoint embed_variable_spine (Δ : Ctx B) (A : Ty B)
  : VariableSpine Δ A → Ren Γ Δ → Tm Γ A.
Proof.
  destruct Δ as [| Δ D]; cbn; intros p ρ;
    [exact (match p with end) |].
  destruct p as [p | p].
  - exact (embed_variable_spine Δ A p (λ T x, ρ T (var_succ x))).
  - exact (embed_spine p (# (ρ D var_zero))).
Defined.

(** Empty spines recover the supplied typed variable, including its
    marker. No equation between context-map functions is needed. *)

(** 空消去链恢复给定的带类型变量及其标记，不需要上下文映射函数间的等式。 *)

Definition embed_variable_spine_var (Δ : Ctx B)
  : ∀ (A : Ty B) (x : Var Δ A) (ρ : Ren Γ Δ),
      embed_variable_spine Δ A (variable_spine Δ A x) ρ = # (ρ A x).
Proof.
  induction Δ as [| Δ ih D]; intros A x ρ;
    [exact (match x with end) |].
  destruct x as [x | x]; cbn.
  - exact (ih A x (λ T y, ρ T (var_succ y))).
  - destruct x. reflexivity.
Defined.

(** Append left projection at the selected context position. *)

(** 在选定上下文位置处追加左投影。 *)

Fixpoint variable_spine_fst (Δ : Ctx B) (A U : Ty B)
  : VariableSpine Δ (A × U) → VariableSpine Δ A.
Proof.
  destruct Δ as [| Δ D]; cbn; intros p;
    [exact (match p with end) |].
  destruct p as [p | p].
  - exact (inl (variable_spine_fst Δ A U p)).
  - exact (inr (spine_fst p)).
Defined.

(** Append right projection without changing the head position. *)

(** 追加右投影而不改变头部位置。 *)

Fixpoint variable_spine_snd (Δ : Ctx B) (A U : Ty B)
  : VariableSpine Δ (A × U) → VariableSpine Δ U.
Proof.
  destruct Δ as [| Δ D]; cbn; intros p;
    [exact (match p with end) |].
  destruct p as [p | p].
  - exact (inl (variable_spine_snd Δ A U p)).
  - exact (inr (spine_snd p)).
Defined.

(** Append application; the raw argument is retained in [Γ]. *)

(** 追加应用；原始实参保留在 [Γ] 中。 *)

Fixpoint variable_spine_app (Δ : Ctx B) (A U : Ty B) (a : Tm Γ A)
  : VariableSpine Δ (A ⇒ U) → VariableSpine Δ U.
Proof.
  destruct Δ as [| Δ D]; cbn; intros p;
    [exact (match p with end) |].
  destruct p as [p | p].
  - exact (inl (variable_spine_app Δ A U a p)).
  - exact (inr (spine_app p a)).
Defined.

(** Projection extension commutes with embedding pointwise. *)

(** 投影延伸与嵌入逐点交换。 *)

Definition embed_variable_spine_fst (Δ : Ctx B)
  : ∀ (A U : Ty B) (p : VariableSpine Δ (A × U)) (ρ : Ren Γ Δ),
      embed_variable_spine Δ A (variable_spine_fst Δ A U p) ρ =
      π₁ (embed_variable_spine Δ (A × U) p ρ).
Proof.
  induction Δ as [| Δ ih D]; intros A U p ρ;
    [exact (match p with end) |].
  destruct p as [p | p]; cbn.
  - exact (ih A U p (λ T x, ρ T (var_succ x))).
  - exact (embed_spine_fst p (# (ρ D var_zero))).
Defined.

(** The right projection has the same pointwise law. *)

(** 右投影满足相同的逐点定律。 *)

Definition embed_variable_spine_snd (Δ : Ctx B)
  : ∀ (A U : Ty B) (p : VariableSpine Δ (A × U)) (ρ : Ren Γ Δ),
      embed_variable_spine Δ U (variable_spine_snd Δ A U p) ρ =
      π₂ (embed_variable_spine Δ (A × U) p ρ).
Proof.
  induction Δ as [| Δ ih D]; intros A U p ρ;
    [exact (match p with end) |].
  destruct p as [p | p]; cbn.
  - exact (ih A U p (λ T x, ρ T (var_succ x))).
  - exact (embed_spine_snd p (# (ρ D var_zero))).
Defined.

(** Application extension likewise preserves the exact raw argument. *)

(** 应用延伸同样保持精确的原始实参。 *)

Definition embed_variable_spine_app (Δ : Ctx B)
  : ∀ (A U : Ty B) (a : Tm Γ A)
      (p : VariableSpine Δ (A ⇒ U)) (ρ : Ren Γ Δ),
      embed_variable_spine Δ U (variable_spine_app Δ A U a p) ρ =
      embed_variable_spine Δ (A ⇒ U) p ρ · a.
Proof.
  induction Δ as [| Δ ih D]; intros A U a p ρ;
    [exact (match p with end) |].
  destruct p as [p | p]; cbn.
  - exact (ih A U a p (λ T x, ρ T (var_succ x))).
  - exact (embed_spine_app p a (# (ρ D var_zero))).
Defined.

End VariableSpines.

Arguments VariableSpine {B} Γ Δ A.

(** ** Extracting the Variable-Headed View

    Fix arbitrary labels and inspect raw constructors. Introductions
    have no such view. Elimination extends the principal child's view;
    arguments are neither searched nor normalized. *)

(** ** 提取变量头视图

    固定任意标签并检查原始构造器。引入形式没有此视图。消去延伸主要子项的
    视图；实参既不被搜索，也不被正规化。 *)

Section SpineExtraction.
Context {B : Type}.

(** Optional inferred-type view of a raw elimination chain. *)

(** 原始消去链的可选推断类型视图。 *)

Fixpoint variable_spine_view {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : option (VariableSpine Γ Γ A)
  := match t in Tm Γ A return option (VariableSpine Γ Γ A) with
     | tm_var x => Some (variable_spine _ _ _ x)
     | tm_fst p => option_map (variable_spine_fst _ _ _ _)
         (@variable_spine_view _ _ p)
     | tm_snd p => option_map (variable_spine_snd _ _ _ _)
         (@variable_spine_view _ _ p)
     | tm_app f a => option_map (variable_spine_app _ _ _ _ a)
         (@variable_spine_view _ _ f)
     | _ => None
     end.

(** Re-embed a view using the original context positions. *)

(** 使用原上下文位置重新嵌入视图。 *)

Definition embed_variable_view {Γ : Ctx B} {A : Ty B}
    (p : VariableSpine Γ Γ A)
  : Tm Γ A
  := embed_variable_spine Γ Γ A p idRen.

(** Extraction preserves native raw syntax, not just beta/eta equations.
    The statement compares terms only, never equality of view witnesses. *)

(** 提取保持原始语法的原生相等，而不只是 βη 方程。陈述只比较项，不比较
    视图见证的相等。 *)

Definition variable_spine_view_reconstruct {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : ∀ p, variable_spine_view t = Some p → embed_variable_view p = t.
Proof.
  induction t; intros p h; cbn [variable_spine_view] in h;
    try discriminate h.
  - injection h as h. subst p. apply embed_variable_spine_var.
  - destruct (variable_spine_view t) as [q |] eqn:view;
      cbn in h; [| discriminate h].
    injection h as h. subst p.
    unfold embed_variable_view. rewrite embed_variable_spine_fst.
    exact (f_equal tm_fst (IHt q eq_refl)).
  - destruct (variable_spine_view t) as [q |] eqn:view;
      cbn in h; [| discriminate h].
    injection h as h. subst p.
    unfold embed_variable_view. rewrite embed_variable_spine_snd.
    exact (f_equal tm_snd (IHt q eq_refl)).
  - destruct (variable_spine_view t1) as [q |] eqn:view;
      cbn in h; [| discriminate h].
    injection h as h. subst p.
    unfold embed_variable_view. rewrite embed_variable_spine_app.
    exact (f_equal (λ f, f · t2) (IHt1 q eq_refl)).
Defined.

(** At product type, absence of a pair introduction leaves an outer
    variable or elimination. Other result types make no assertion. *)

(** 在积类型处，配对引入缺失意味着最外层为变量或消去。其他结果类型不作
    断言。 *)

Definition product_absent_neutral {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : match A as T return Tm Γ T → Type with
    | ty_prod D V => λ t, pair_parts t = None → is_neutral_tm t
    | _ => λ _, unit
    end t.
Proof.
  destruct t; cbn; try exact tt;
    try (destruct A; cbn; exact tt || exact (λ _, tt));
    try (destruct U; cbn; exact tt || exact (λ _, tt)).
  intros h. discriminate h.
Defined.

(** At function type the corresponding observer is the lambda body. *)

(** 在函数类型处，对应观测为 λ 项体。 *)

Definition function_absent_neutral {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : match A as T return Tm Γ T → Type with
    | ty_arr D V => λ t, lambda_body t = None → is_neutral_tm t
    | _ => λ _, unit
    end t.
Proof.
  destruct t; cbn; try exact tt;
    try (destruct A; cbn; exact tt || exact (λ _, tt));
    try (destruct U; cbn; exact tt || exact (λ _, tt)).
  intros h. discriminate h.
Defined.

(** Every neutral head-terminal term has a variable-headed view, even
    when its arguments contain redexes. This is a constructive discovery
    of a view, not a uniqueness claim about differently aligned views. *)

(** 每个外层中性、头部终止的项都有变量头视图，即使实参中有可归约式。
    这是构造性地发现视图，不声称不同对齐视图之间的唯一性。 *)

Definition head_terminal_variable_spine {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : head_contractum t = None → is_neutral_tm t →
      ∃ p, variable_spine_view t = Some p.
Proof.
  induction t; intros terminal neutral; cbn in neutral;
    try exact (match neutral with end).
  - exists (variable_spine Γ Γ A v). reflexivity.
  - cbn [head_contractum] in terminal.
    destruct (pair_parts t) as [[a u] |] eqn:parts;
      [discriminate terminal |].
    destruct (head_contractum t) as [u |] eqn:step;
      cbn in terminal; [discriminate terminal |].
    destruct (IHt eq_refl (product_absent_neutral t parts)) as [p view].
    exists (variable_spine_fst Γ Γ A U p).
    cbn [variable_spine_view]. rewrite view. reflexivity.
  - cbn [head_contractum] in terminal.
    destruct (pair_parts t) as [[a u] |] eqn:parts;
      [discriminate terminal |].
    destruct (head_contractum t) as [u |] eqn:step;
      cbn in terminal; [discriminate terminal |].
    destruct (IHt eq_refl (product_absent_neutral t parts)) as [p view].
    exists (variable_spine_snd Γ Γ A U p).
    cbn [variable_spine_view]. rewrite view. reflexivity.
  - cbn [head_contractum] in terminal.
    destruct (lambda_body t1) as [q |] eqn:body;
      [discriminate terminal |].
    destruct (head_contractum t1) as [u |] eqn:step;
      cbn in terminal; [discriminate terminal |].
    destruct (IHt1 eq_refl (function_absent_neutral t1 body)) as [p view].
    exists (variable_spine_app Γ Γ A U t2 p).
    cbn [variable_spine_view]. rewrite view. reflexivity.
Defined.

(** Every non-pair product head at the remaining eta-root boundary has
    an inferred-type view that reconstructs it natively. This includes
    the blocked projection and application targets, but does not yet
    prove joint injectivity of their two projection views. *)

(** 剩余 η 根边界处每个非配对积头部都有能原生重构它的推断类型视图。这
    包括阻塞的投影及应用目标，但尚未证明其两个投影视图联合单射。 *)

Definition head_terminal_product_spine {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ (A × U)) (terminal : head_contractum t = None)
    (parts : pair_parts t = None)
  : ∃ p, variable_spine_view t = Some p ∧ embed_variable_view p = t.
Proof.
  destruct (head_terminal_variable_spine t terminal
    (product_absent_neutral t parts)) as [p view].
  exists p. exact (view, variable_spine_view_reconstruct t p view).
Defined.

End SpineExtraction.
