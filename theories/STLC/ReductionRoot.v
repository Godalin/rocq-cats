From Cats.STLC Require Export ReductionSource.

(** * Observing Root Beta Contraction

    A root redex has at most one contractum. Obtain this fact by observing
    the typed source, rather than injecting equal dependent constructors.
    The observation also distinguishes introductions from eliminations.
    No equality decision on base labels or uniqueness of identity proofs
    is needed. This concerns root contraction only: contextual beta is
    generally nondeterministic. *)

(** * 观测根 β 收缩

    根可归约式至多有一个收缩结果。通过观测带类型的源项取得此性质，避免对
    相等的依赖构造器作单射消去。观测也区分引入与消去形式，不需要基类型标签
    相等可判定或恒等证明唯一性。这里只讨论根收缩：上下文 β 通常不确定。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Typed Introduction Observers

    Fix arbitrary base labels. The observer's result depends on the
    simple type: a function may expose a body and a product may expose
    two components. Other types return the unit type. Matching on the
    source term keeps all hidden types and binder contexts aligned. *)

(** ** 带类型的引入观测

    固定任意基类型标签。观测结果依赖简单类型：函数可以暴露项体，积可以暴露
    两个分量；其他类型返回单位类型。对源项作模式匹配，保持隐藏类型和绑定
    上下文一致。 *)

Section IntroductionObservers.
Context {B : Type}.

(** The optional body of a function introduction, or unit at other types. *)

(** 函数引入的可选项体；在其他类型处为单位。 *)

Definition LambdaBody (Γ : Ctx B) (A : Ty B)
  : Type
  := match A with
  | ty_arr U V => option (Tm (Γ ▻ U) V)
  | _ => unit
  end.

(** An absent function body, at every simple type. *)

(** 在每个简单类型处表示缺失的函数项体。 *)

Definition lambda_body_none (Γ : Ctx B) (A : Ty B)
  : LambdaBody Γ A.
Proof. destruct A; exact tt || exact None. Defined.

(** Only an actual lambda exposes a body; variables and eliminations do
    not, even when their result type is an arrow. *)

(** 只有实际的 λ 才暴露项体；变量和消去形式即使结果类型为箭头，也不暴露。 *)

Definition lambda_body {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : LambdaBody Γ A.
Proof.
  destruct t.
  - exact (lambda_body_none _ _).
  - exact tt.
  - exact tt.
  - exact (lambda_body_none _ _).
  - exact (lambda_body_none _ _).
  - exact (Some t).
  - exact (lambda_body_none _ _).
Defined.

(** The optional components of a product introduction. *)

(** 积引入的可选分量。 *)

Definition PairParts (Γ : Ctx B) (A : Ty B)
  : Type
  := match A with
  | ty_prod U V => option (Tm Γ U * Tm Γ V)
  | _ => unit
  end.

(** Absent product components at every simple type. *)

(** 在每个简单类型处表示缺失的积分量。 *)

Definition pair_parts_none (Γ : Ctx B) (A : Ty B)
  : PairParts Γ A.
Proof. destruct A; exact tt || exact None. Defined.

(** Only a pair exposes components; no dependent injection is used. *)

(** 只有配对才暴露分量；不使用依赖单射消去。 *)

Definition pair_parts {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : PairParts Γ A.
Proof.
  destruct t.
  - exact (pair_parts_none _ _).
  - exact tt.
  - exact (Some (t1, t2)).
  - exact (pair_parts_none _ _).
  - exact (pair_parts_none _ _).
  - exact tt.
  - exact (pair_parts_none _ _).
Defined.

(** A discovered body reconstructs the original term by homogeneous
    syntax equality. The empty observation makes no assertion. *)

(** 发现的项体以同类型语法相等重构原项；缺失的观测不作断言。 *)

Definition lambda_body_spec {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : match A as U return Tm Γ U → LambdaBody Γ U → Type with
    | ty_arr U V => λ f p,
        match p with Some q => f = ƛ q | None => unit end
    | _ => λ _ _, unit
    end t (lambda_body t).
Proof.
  destruct t; cbn; try destruct A; try destruct U;
    reflexivity || exact tt.
Defined.

(** Discovered components likewise reconstruct a pair. *)

(** 发现的分量同样重构配对。 *)

Definition pair_parts_spec {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : match A as U return Tm Γ U → PairParts Γ U → Type with
    | ty_prod U V => λ p q,
        match q with Some z => p = ⟨fst z, snd z⟩ | None => unit end
    | _ => λ _ _, unit
    end t (pair_parts t).
Proof.
  destruct t; cbn; try destruct A; try destruct U;
    reflexivity || exact tt.
Defined.

(** Inspect the outer elimination and its immediate introduction. The
    result is a partial computation, not a search under constructors. *)

(** 检查外层消去及其紧邻引入。结果是部分计算，不搜索构造器内部。 *)

Definition root_contractum {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : option (Tm Γ A)
  := match t in Tm Γ A return option (Tm Γ A) with
  | tm_fst p => option_map fst (pair_parts p)
  | tm_snd p => option_map snd (pair_parts p)
  | tm_app f a => option_map (λ p, p[a/]) (lambda_body f)
  | _ => None
  end.

(** Renaming cannot turn a non-lambda into a lambda. The specialized
    equation also records how a discovered body changes under a binder. *)

(** 重命名不能将非 λ 变成 λ；这个专化等式也记录发现的项体如何在绑定下变化。 *)

Definition lambda_body_rename {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (ρ : Ren Δ Γ),
      match A as U return
        LambdaBody Δ U → LambdaBody Γ U → Prop with
      | ty_arr U V => λ q p,
          q = option_map (λ p, p⟨ρ^↑Ren⟩) p
      | _ => λ _ _, True
      end (lambda_body t⟨ρ⟩) (lambda_body t).
Proof.
  destruct t; intros Δ ρ; cbn; try destruct A; try destruct U;
    reflexivity || exact I.
Defined.

(** Renaming product components is equally structural. *)

(** 积分量的重命名同样由结构决定。 *)

Definition pair_parts_rename {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (ρ : Ren Δ Γ),
      match A as U return PairParts Δ U → PairParts Γ U → Prop with
      | ty_prod U V => λ q p,
          q = option_map (λ p, ((fst p)⟨ρ⟩, (snd p)⟨ρ⟩)) p
      | _ => λ _ _, True
      end (pair_parts t⟨ρ⟩) (pair_parts t).
Proof.
  destruct t; intros Δ ρ; cbn; try destruct A; try destruct U;
    reflexivity || exact I.
Defined.

(** Root observation commutes with renaming, including the function beta
    substitution. This uses the existing single-substitution equation. *)

(** 根观测与重命名交换，包括函数 β 的替换；复用既有单变量替换等式。 *)

Definition root_contractum_rename {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    (Δ : Ctx B) (ρ : Ren Δ Γ)
  : root_contractum t⟨ρ⟩ = option_map (λ u, u⟨ρ⟩) (root_contractum t).
Proof.
  destruct t; cbn; try reflexivity.
  - rewrite (pair_parts_rename t Δ ρ).
    destruct (pair_parts t) as [[p q] |]; reflexivity.
  - rewrite (pair_parts_rename t Δ ρ).
    destruct (pair_parts t) as [[p q] |]; reflexivity.
  - rewrite (lambda_body_rename t1 Δ ρ).
    destruct (lambda_body t1) as [p |]; cbn; [| reflexivity].
    f_equal. symmetry. apply rename_single.
Defined.

End IntroductionObservers.

(** A root derivation determines the observation. Only the derivation's
    own constructors are eliminated, with their indices generalized. *)

(** 根推导确定观测结果；只在索引泛化后消去该推导自身的构造器。 *)

Definition root_beta_contractum@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootBeta@{b e _} t u)
  : root_contractum t = Some u.
Proof. destruct h; reflexivity. Defined.

(** Every successful observation reconstructs a root derivation. These
    two maps characterize the relation without identifying its witnesses. *)

(** 每个成功观测都重构根推导；双向映射刻画关系，而不识别其见证。 *)

Definition root_contractum_beta@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : root_contractum t = Some u → RootBeta@{b e _} t u.
Proof.
  destruct t; cbn; intros h; try discriminate h.
  - pose proof (pair_parts_spec t) as p.
    destruct (pair_parts t) as [[v w] |]; cbn in *;
      [| discriminate h].
    injection h as h. subst u. rewrite p. constructor.
  - pose proof (pair_parts_spec t) as p.
    destruct (pair_parts t) as [[v w] |]; cbn in *;
      [| discriminate h].
    injection h as h. subst u. rewrite p. constructor.
  - pose proof (lambda_body_spec t1) as p.
    destruct (lambda_body t1) as [v |]; cbn in *;
      [| discriminate h].
    injection h as h. subst u. rewrite p. constructor.
Defined.

(** Two root targets are equal as syntax trees. No equality of root
    witnesses, and no determinism of contextual reduction, is asserted. *)

(** 两个根目标作为语法树相等；不要求根见证相等，也不断言上下文归约确定。 *)

Definition root_beta_unique@{b r s +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}
    (h : RootBeta@{b r _} t u) (k : RootBeta@{b s _} t v)
  : u = v.
Proof.
  pose proof (root_beta_contractum h) as p.
  rewrite (root_beta_contractum k) in p. now injection p.
Defined.

(** A root step after renaming comes from an original root step. Renaming
    may identify variables; injectivity is unnecessary because it preserves
    introduction forms. The target is reconstructed, not inverted as a
    dependent constructor equality. *)

(** 重命名后的根步骤来自原来的根步骤。重命名可以合并变量；它保持引入形式，
    因而无须单射。目标通过重构取得，不对依赖构造器等式作反演。 *)

Definition root_beta_rename_inv@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    (Δ : Ctx B) (ρ : Ren Δ Γ) {u : Tm Δ A}
    (h : RootBeta@{b e _} t⟨ρ⟩ u)
  : ∃ v, RootBeta@{b e _} t v ∧ u = v⟨ρ⟩.
Proof.
  pose proof (root_beta_contractum h) as p.
  rewrite root_contractum_rename in p.
  destruct (root_contractum t) as [v |] eqn:q; cbn in p;
    [| discriminate p].
  exists v. split.
  - exact (root_contractum_beta t v q).
  - now injection p as p.
Defined.

(** A root contraction of an elimination requires an introduction in its
    head position. A neutral head therefore rules out the root branch.
    This statement analyzes the whole typed source before specialization. *)

(** 消去的根收缩要求头位置为引入形式，因此中性头排除根分支。这个陈述先
    分析整个带类型源项，再供各个消去形式专化使用。 *)

Definition root_beta_intro_source@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootBeta@{b e _} t u)
  : match t with
    | tm_fst p | tm_snd p => is_neutral_tm p → Empty_set
    | tm_app f _ => is_neutral_tm f → Empty_set
    | _ => unit
    end.
Proof. destruct h; cbn; exact (λ n, n). Defined.
