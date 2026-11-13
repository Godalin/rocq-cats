From Cats.STLC Require Export Reduction.
From Cats.Set.Relation Require Import Compatible.

(** * Directed Beta Reduction and Substitution

    A beta step remains one beta step after simultaneous substitution.
    Renaming is the special case assigning only variables. These facts
    concern the already defined directed [BetaStep], including reduction
    under binders, and do not use NbE or a termination argument.

    First fold the generic compatible closure into a relation quantified
    over substitutions. Only preservation of the root rules is then
    specific to beta. The same fold can be reused for other root systems
    whose substituted generators have contextual realizations. *)

(** * 有向 β 归约与替换

    一个 β 步骤经过同时替换后仍是一个 β 步骤。重命名是只赋予变量的特例。
    这些结论针对已经定义的有向 [BetaStep]，包括绑定之下的归约，不使用 NbE
    或终止性论证。

    首先将一般相容闭包折叠到对所有替换量化的关系中，随后只有根规则的保持性
    是 β 特有的。若其他根规则经过替换后也有上下文实现，同一个折叠即可复用。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Substitution into Contextual Steps

    Fix the signature and a target root relation. Quantifying over all
    destination contexts and substitutions gives a compatible relation:
    each constructor acts on the substituted terms, and abstraction uses
    the lifted substitution. No equality of assignment functions is needed. *)

(** ** 对上下文步骤作替换

    固定签名与目标根关系。对所有目标上下文和替换量化后得到相容关系：每个
    构造器作用于替换后的项，抽象则使用提升的替换，不需要赋值函数相等。 *)

Section ContextSubstitution.
Universes b e.
Context {B : Type@{b}} (S : TmRelation@{b e _} B).

(** All one-hole constructors preserve the substitution-quantified target. *)

(** 全部单孔构造器保持对替换量化的目标关系。 *)

Definition context_subst_compatible
  : is_compatible (TmContexts B)
      (λ i t u, ∀ Δ (σ : Sub Δ (fst i)),
        ContextStep S t[σ] u[σ]).
Proof.
  intros i j c t u h Δ σ. destruct c; cbn in *.
  - exact (context_step_lift S (op_pair_l u0[σ]) (h Δ σ)).
  - exact (context_step_lift S (op_pair_r t0[σ]) (h Δ σ)).
  - exact (context_step_lift S op_fst (h Δ σ)).
  - exact (context_step_lift S op_snd (h Δ σ)).
  - exact (context_step_lift S op_lam (h _ (σ^↑Sub))).
  - exact (context_step_lift S (op_app_l u0[σ]) (h Δ σ)).
  - exact (context_step_lift S (op_app_r t0[σ]) (h Δ σ)).
Defined.

End ContextSubstitution.

(** If every substituted source generator has a contextual target step,
    the same holds for its entire compatible closure. The two root
    relations have independently inferred witness universes. *)

(** 若每个经过替换的源生成元都有目标上下文步骤，其整个相容闭包也如此。
    两个根关系的见证宇宙独立推导。 *)

Definition context_step_subst@{b r s +} {B : Type@{b}}
    (R : TmRelation@{b r _} B) (S : TmRelation@{b s _} B)
    (hr : ∀ Γ A (t u : Tm Γ A), R Γ A t u →
      ∀ Δ (σ : Sub Δ Γ), ContextStep S t[σ] u[σ])
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ContextStep R t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : ContextStep S t[σ] u[σ]
  := context_closure_preserves (TmContexts B)
      (context_subst_compatible S)
      (λ i x y p, hr (fst i) (snd i) x y p)
      (Γ, A) t u h Δ σ.

(** ** Beta Generators and Their Contexts

    Fix a signature, with arbitrary base labels. Function beta uses the
    existing law commuting simultaneous and single-variable substitution;
    product beta commutes definitionally. The generic fold then handles
    every enclosing constructor, including abstractions.

    The signature bound [b] and step-evidence bound [e] remain separate,
    with [b <= e]. Boundary annotations prevent universe minimization from
    silently restricting a public theorem to equal levels. Calls can still
    infer these parameters from their arguments and expected results. *)

(** ** β 生成元及其上下文

    固定任意基类型标签的签名。函数 β 使用已有的同时替换与单变量替换交换律，
    积 β 则按定义交换。一般折叠随后处理全部外层构造器，包括抽象。

    签名界 [b] 与步骤证据界 [e] 保持分离，满足 [b <= e]。边界标注防止宇宙
    最小化悄悄将公开定理限制为同层情形；调用时仍可从参数及预期结果推导它们。 *)

Section BetaSubstitution.
Universes b e.
Context {B : Type@{b}}.

(** Substitution preserves a root contraction at the root itself. *)

(** 替换保持根部的收缩，其结果仍是根收缩。 *)

Definition root_beta_subst {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootBeta@{b e _} t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : RootBeta@{b e _} t[σ] u[σ].
Proof.
  destruct h; cbn.
  - rewrite subst_single. exact (root_beta_function t[σ^↑Sub] u[σ]).
  - exact (root_beta_fst t[σ] u[σ]).
  - exact (root_beta_snd t[σ] u[σ]).
Defined.

(** Preservation for a full contextual beta step reuses the general fold. *)

(** 完整上下文 β 步骤的保持性复用一般折叠。 *)

Definition beta_step_subst {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : BetaStep@{b e _ _} t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : BetaStep@{b e _ _} t[σ] u[σ]
  := context_step_subst (@RootBeta@{b e _} B) (@RootBeta@{b e _} B)
      (λ Γ A t u p Δ σ,
        context_step_root _ (root_beta_subst p Δ σ)) h Δ σ.

(** Renaming preservation follows by substitution with variable terms. *)

(** 以变量项作替换，即得重命名保持性。 *)

Definition beta_step_rename {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : BetaStep@{b e _ _} t u) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : BetaStep@{b e _ _} t⟨ρ⟩ u⟨ρ⟩.
Proof.
  rewrite <- !subst_ren.
  exact (beta_step_subst h Δ (RenSub ρ)).
Defined.

(** Every one-hole term operation preserves beta steps. *)

(** 每个单孔项操作都保持 β 步骤。 *)

Definition beta_step_lift {Γ Δ : Ctx B} {A U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : BetaStep@{b e _ _} t u)
  : BetaStep@{b e _ _} (TmContexts B (Γ, A) (Δ, U) c t)
      (TmContexts B (Γ, A) (Δ, U) c u)
  := context_step_lift (@RootBeta@{b e _} B) c h.

(** Finite directed paths retain the same substitution. No backward edges
    or eta rules are introduced. *)

(** 有限有向路径也保持同一替换，不引入反向边或 η 规则。 *)

Definition beta_rtc_subst {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ((@BetaStep@{b e _ _} B Γ A)^*) t u) (Δ : Ctx B) (σ : Sub Δ Γ)
  : ((@BetaStep@{b e _ _} B Δ A)^*) t[σ] u[σ]
  := rtc_preserves (λ v, v[σ])
      (λ x y p, rtc_step (beta_step_subst p Δ σ)) h.

(** Renaming acts on each edge of a directed path. *)

(** 重命名作用于有向路径的每条边。 *)

Definition beta_rtc_rename {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ((@BetaStep@{b e _ _} B Γ A)^*) t u) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : ((@BetaStep@{b e _ _} B Δ A)^*) t⟨ρ⟩ u⟨ρ⟩
  := rtc_preserves (λ v, v⟨ρ⟩)
      (λ x y p, rtc_step (beta_step_rename p Δ ρ)) h.

(** A fixed one-hole context lifts the entire path, including its empty
    case; it can change the judgement, as abstraction does. *)

(** 固定单孔上下文提升整条路径，包括空路径；它可以像抽象那样改变判断。 *)

Definition beta_rtc_lift {Γ Δ : Ctx B} {A U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : ((@BetaStep@{b e _ _} B Γ A)^*) t u)
  : ((@BetaStep@{b e _ _} B Δ U)^*) (TmContexts B (Γ, A) (Δ, U) c t)
      (TmContexts B (Γ, A) (Δ, U) c u)
  := rtc_preserves (TmContexts B (Γ, A) (Δ, U) c)
      (λ x y p, rtc_step (beta_step_lift c p)) h.

(** Both pair components may follow their own finite paths. Concatenate
    the left path, with the old right component fixed, and the right path,
    with the new left component fixed. *)

(** 配对的两个分量可以分别沿有限路径归约：先固定旧右分量提升左路径，再固定
    新左分量提升右路径，最后连接两条路径。 *)

Definition beta_rtc_pair {Γ : Ctx B} {A U : Ty B}
    {t t' : Tm Γ A} {u u' : Tm Γ U}
    (h : ((@BetaStep@{b e _ _} B Γ A)^*) t t')
    (k : ((@BetaStep@{b e _ _} B Γ U)^*) u u')
  : ((@BetaStep@{b e _ _} B Γ (A × U))^*) (⟨t, u⟩) (⟨t', u'⟩)
  := rtc_trans (beta_rtc_lift (op_pair_l u) h)
      (beta_rtc_lift (op_pair_r t') k).

(** The same directed concatenation handles function and argument paths. *)

(** 同样的有向连接处理函数与实参各自的路径。 *)

Definition beta_rtc_app {Γ : Ctx B} {A U : Ty B}
    {f f' : Tm Γ (A ⇒ U)} {u u' : Tm Γ A}
    (h : ((@BetaStep@{b e _ _} B Γ (A ⇒ U))^*) f f')
    (k : ((@BetaStep@{b e _ _} B Γ A)^*) u u')
  : ((@BetaStep@{b e _ _} B Γ U)^*) (f · u) (f' · u')
  := rtc_trans (beta_rtc_lift (op_app_l u) h)
      (beta_rtc_lift (op_app_r f') k).

End BetaSubstitution.

(** ** Reducing the Assigned Terms

    Fix a signature. Now allow each assignment to follow a finite beta
    path. Substitution into a term can duplicate or discard an assignment,
    so the result is a finite path, not necessarily a single step. The
    proof uses the syntax induction and directed constructor lifts above.
    The path bound [p] can lie strictly above the step bound [e]; only
    [b <= e <= p] is needed. *)

(** ** 归约被赋予的项

    固定签名。现在允许每个赋值分别沿有限 β 路径归约。项的替换可以复制或
    丢弃某个赋值，因此结果是有限路径，未必是单独一步。证明使用语法归纳及
    上面的有向构造器提升。路径界 [p] 可以严格高于步骤界 [e]，只需
    [b <= e <= p]。 *)

Section AssignmentReduction.
Universes b e p.
Context {B : Type@{b}}.

(** Lift assignment paths under a binder: old assignments are weakened,
    and the fresh variable follows an empty path. *)

(** 将赋值路径提升到绑定之下：旧赋值作弱化，新变量则沿空路径。 *)

Definition sub_lift_beta_rtc {Γ Δ : Ctx B} {A : Ty B}
    {σ τ : Sub Δ Γ}
    (h : ∀ U x, ReflTransClosure@{b e p}
      (@BetaStep@{b e _ _} B Δ U) (σ U x) (τ U x))
  : ∀ U x, ReflTransClosure@{b e p}
      (@BetaStep@{b e _ _} B (Δ ▻ A) U)
      ((σ^↑Sub) U x) ((τ^↑Sub) U x).
Proof.
  intros U [x | x]; cbn.
  - exact (beta_rtc_rename (h U x) _ wkRen).
  - exact (rtc_refl _).
Defined.

(** Reducing all assigned terms pointwise gives a directed path between
    the substituted terms, without equality of substitution functions. *)

(** 逐点归约全部赋值，得到替换结果之间的有向路径，无须替换函数相等。 *)

Definition subst_beta_rtc {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (σ τ : Sub Δ Γ),
      (∀ U x, ReflTransClosure@{b e p}
        (@BetaStep@{b e _ _} B Δ U) (σ U x) (τ U x)) →
      ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] t[τ].
Proof.
  induction t; intros Δ σ τ h; cbn.
  - exact (h A v).
  - exact (rtc_refl _).
  - exact (beta_rtc_pair (IHt1 Δ σ τ h) (IHt2 Δ σ τ h)).
  - exact (beta_rtc_lift op_fst (IHt Δ σ τ h)).
  - exact (beta_rtc_lift op_snd (IHt Δ σ τ h)).
  - exact (beta_rtc_lift op_lam
      (IHt _ (σ^↑Sub) (τ^↑Sub) (sub_lift_beta_rtc h))).
  - exact (beta_rtc_app (IHt1 Δ σ τ h) (IHt2 Δ σ τ h)).
Defined.

(** Both the expression and its assignments can reduce. First follow the
    expression path under the old assignment, then change the assignments. *)

(** 表达式及其赋值均可归约：先在旧赋值下沿表达式路径，再改变赋值。 *)

Definition beta_rtc_subst_both {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ A) t u)
    {Δ : Ctx B} {σ τ : Sub Δ Γ}
    (k : ∀ U x, ReflTransClosure@{b e p}
      (@BetaStep@{b e _ _} B Δ U) (σ U x) (τ U x))
  : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] u[τ]
  := rtc_trans (beta_rtc_subst h Δ σ) (subst_beta_rtc u Δ σ τ k).

(** Replacing the newest variable by an argument path is the single-input
    case. Unused arguments produce empty paths; repeated uses produce
    separate copies of the argument path. *)

(** 沿实参路径代入最新变量，是单输入情形。未使用的实参产生空路径，重复
    使用则为实参路径产生多个副本。 *)

Definition beta_rtc_single {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) {u u' : Tm Γ A}
    (h : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ A) u u')
  : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ U) t[u/] t[u'/].
Proof.
  apply subst_beta_rtc. intros V [x | x]; cbn.
  - exact (rtc_refl _).
  - destruct x. exact h.
Defined.

End AssignmentReduction.
