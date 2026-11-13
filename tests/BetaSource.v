From Cats.STLC Require Import ReductionSource.
From Cats.Set.Relation Require Import Compatible.

(** * Beta Source-Analysis Regressions

    Check source views at separate and equal syntax/step levels, and
    neutral expansion with predicates both smaller and larger than step
    evidence. Concrete observations distinguish root, left/right child
    and binder cases in transparent derivations. *)

(** * β 来源分析回归检查

    在语法／步骤层级分离及相等时检查源视图，并检查谓词小于或大于步骤证据
    时的中性展开。具体观测区分透明推导中的根、左／右子项及绑定分支。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Separate Syntax and Step Universes

    Fix [b < e < l] with arbitrary base labels. Analysis and reconstruction
    keep step evidence at [e], while lambda inversion changes context. *)

(** ** 分离的语法与步骤宇宙

    固定 [b < e < l] 及任意基类型标签。分析与重构将步骤证据保持在 [e]，
    而 λ 反演改变上下文。 *)

Section SeparatedLevels.
Universes b e l.
Constraint b < e, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Analysis retains the larger step universe. *)

(** 分析保留较大的步骤宇宙。 *)

Definition separated_beta_source {t u : Tm Γ A}
    (h : BetaStep@{b e l b} t u)
  : BetaSource@{b e l} t u
  := beta_step_source h.

(** Reconstructing a source view also keeps that universe. *)

(** 源视图的重构同样保持该宇宙。 *)

Definition separated_source_step {t u : Tm Γ A}
    (h : BetaSource@{b e l} t u)
  : BetaStep@{b e l b} t u
  := beta_source_step t u h.

(** Binder inversion returns a body in the extended context without label
    equality decisions or a fiber-injection assumption. *)

(** 绑定反演返回扩张上下文中的项体，不需要标签相等判定或纤维单射假设。 *)

Definition separated_lambda_source {U : Ty B}
    {t : Tm (Γ ▻ A) U} {u : Tm Γ (A ⇒ U)}
    (h : BetaStep@{b e l b} (ƛ t) u)
  : ∃ t', BetaStep@{b e l b} t t' ∧ u = ƛ t'
  := beta_step_lam_inv h.

(** The hidden domain of an application is retained in its child cases. *)

(** 应用的隐藏定义域保留在其子项分支中。 *)

Definition separated_application_source {U : Ty B}
    {f : Tm Γ (A ⇒ U)} {a : Tm Γ A} {u : Tm Γ U}
    (h : BetaStep@{b e l b} (f · a) u)
  : RootBeta@{b e b} (f · a) u ∨
    ((∃ f', BetaStep@{b e l b} f f' ∧ u = f' · a) ∨
     (∃ a', BetaStep@{b e l b} a a' ∧ u = f · a'))
  := beta_step_app_inv h.

End SeparatedLevels.

(** ** Equal Syntax and Step Universes

    Fix [b = e] and a larger classification bound. The source view does
    not require strict separation of syntax and actual step data. *)

(** ** 相同的语法与步骤宇宙

    固定 [b = e] 及较大的分类界。源视图不要求语法与实际步骤数据严格分离。 *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Both directions remain available at the common bound. *)

(** 在共同界内仍有双向映射。 *)

Definition equal_level_source_iff (t u : Tm Γ A)
  : BetaStep@{b b l b} t u ↔ BetaSource@{b b l} t u
  := beta_step_source_iff t u.

End EqualLevels.

(** ** Predicates Smaller than the Syntax

    Fix [p < b < e < l]. Expansion may return small data even though it
    inspects a larger step witness and its reconstructed target equation. *)

(** ** 小于语法的谓词

    固定 [p < b < e < l]。即使展开检查较大的步骤见证与目标重构等式，也可以
    返回小数据。 *)

Section SmallerPredicate.
Universes p b e l.
Constraint p < b, b < e, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.
Context (P : Tm Γ A → Type@{p}).
Context (hp : ∀ t, is_neutral_tm t →
  (∀ u, BetaStep@{b e l b} t u → P u) → P t).

(** Application expansion imposes no lower bound on predicate data. *)

(** 应用展开不对谓词数据施加额外下界。 *)

Definition smaller_predicate_application {U : Ty B}
    (f : Tm Γ (U ⇒ A)) (a : Tm Γ U)
    (hr : ∀ u, RootBeta@{b e b} (f · a) u → P u)
    (hf : ∀ f', BetaStep@{b e l b} f f' → P (f' · a))
    (ha : ∀ a', BetaStep@{b e l b} a a' → P (f · a'))
  : P (f · a)
  := neutral_expansion_app hp f a hr hf ha.

End SmallerPredicate.

(** ** Predicates Larger than the Classification Bound

    Reverse the order to [b < e < l < p]. The expansion law has its own
    auxiliary bound and does not force predicate data below [l]. *)

(** ** 大于分类界的谓词

    将顺序改为 [b < e < l < p]。展开律另有辅助界，不迫使谓词数据低于 [l]。 *)

Section LargerPredicate.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.
Context (P : Tm Γ A → Type@{p}).
Context (hp : ∀ t, is_neutral_tm t →
  (∀ u, BetaStep@{b e l b} t u → P u) → P t).

(** Variable expansion returns the larger predicate witness directly. *)

(** 变量展开直接返回较大的谓词见证。 *)

Definition larger_predicate_variable (x : Var Γ A)
  : P (# x)
  := neutral_expansion_var hp x.

End LargerPredicate.

(** ** Observable Source Cases

    Use the empty base signature and unit/product/function types. Observe
    the branch selected by the constructed reduction, not an asserted
    uniqueness of all reductions from the same term. *)

(** ** 可观测的来源分支

    使用空基签名及单位／积／函数类型。观测所构造归约选择的分支，不声称同一
    项的全部归约都具有唯一来源。 *)

Section Computations.

(** A closed unit redex and its original root-step witness. *)

(** 闭单位可归约式及其原根步骤见证。 *)

Definition source_unit_redex
  : Tm (∅ : Ctx Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** Root witnesses embed into the existing contextual relation. *)

(** 根见证嵌入已有上下文关系。 *)

Definition source_unit_step
  : BetaStep source_unit_redex ⋆
  := context_step_root _ (root_beta_function (# var_zero) ⋆).

(** Observe which pair component changed. *)

(** 观测配对的哪个分量改变。 *)

Definition pair_source_tag {Γ : Ctx Empty_set} {A U : Ty Empty_set}
    {p : Tm Γ A} {q : Tm Γ U} {u : Tm Γ (A × U)}
    (h : BetaStep (⟨p, q⟩) u)
  : bool
  := match beta_step_pair_inv h with inl _ => false | inr _ => true end.

(** The left-child tag computes from the original closure witness. *)

(** 左子项标签从原闭包见证计算得出。 *)

Example pair_left_source_computes
  : pair_source_tag
      (context_step_lift _ (op_pair_l ⋆) source_unit_step) = false.
Proof. reflexivity. Qed.

(** Reconstructing a right-child source view preserves that tag. *)

(** 重构右子项源视图，保持该分支标签。 *)

Example pair_right_reconstruction_computes
  : pair_source_tag
      (beta_source_step (⟨⋆, source_unit_redex⟩) (⟨⋆, ⋆⟩)
        (inr (existT _ ⋆ (source_unit_step, eq_refl)))) = true.
Proof. reflexivity. Qed.

(** Observe root/function/argument alternatives by three distinct tags. *)

(** 用三个不同标签观测根／函数／实参备选。 *)

Definition app_source_tag {Γ : Ctx Empty_set} {A U : Ty Empty_set}
    {f : Tm Γ (A ⇒ U)} {a : Tm Γ A} {u : Tm Γ U}
    (h : BetaStep (f · a) u)
  : nat
  := match beta_step_app_inv h with
  | inl _ => 0
  | inr (inl _) => 1
  | inr (inr _) => 2
  end.

(** A function beta contraction selects the root alternative. *)

(** 函数 β 收缩选择根分支。 *)

Example application_root_source_computes
  : app_source_tag source_unit_step = 0.
Proof. reflexivity. Qed.

(** The unit identity is also an argument of a higher-order redex. *)

(** 单位恒等函数也可作为高阶可归约式的实参。 *)

Definition source_unit_identity
  : Tm (∅ : Ctx Empty_set) (⊤ ⇒ ⊤)
  := ƛ (# var_zero).

(** Reducing that higher-order function position keeps its own tag. *)

(** 归约该高阶函数位置，保持自身的标签。 *)

Example application_function_source_computes
  : app_source_tag (context_step_lift _ (op_app_l ⋆)
      (context_step_root _
        (root_beta_function (# var_zero) source_unit_identity))) = 1.
Proof. reflexivity. Qed.

(** An argument step is distinct from reducing the outer root redex. *)

(** 实参步骤与归约外层根可归约式有不同标签。 *)

Example application_argument_source_computes
  : app_source_tag (context_step_lift _ (op_app_r source_unit_identity)
      source_unit_step) = 2.
Proof. reflexivity. Qed.

(** A projection contraction exposes an actual root witness. *)

(** 投影收缩暴露实际的根见证。 *)

Example projection_root_source_computes
  : match beta_step_fst_inv
      (context_step_root _ (root_beta_fst
        (tm_unit : Tm (∅ : Ctx Empty_set) ⊤) ⋆)) with
    | inl _ => true
    | inr _ => false
    end = true.
Proof. reflexivity. Qed.

(** Reduction under second projection retains the reduced input as data. *)

(** 第二投影之下的归约，将归约后的输入保留为数据。 *)

Example projection_child_source_computes
  : match beta_step_snd_inv (context_step_lift _ op_snd
      (context_step_root _ (root_beta_function (# var_zero)
        (⟨tm_unit, tm_unit⟩ : Tm (∅ : Ctx Empty_set) (⊤ × ⊤))))) with
    | inl _ => false
    | inr _ => true
    end = true.
Proof. reflexivity. Qed.

(** Binder inversion returns the actual target body, preserving its scope. *)

(** 绑定反演返回实际的目标项体，保持其作用域。 *)

Example lambda_body_source_computes
  : projT1 (beta_step_lam_inv (context_step_lift _ op_lam
      (context_step_root _ (root_beta_function (# var_zero)
        (# var_zero : Tm ((∅ : Ctx Empty_set) ▻ ⊤) ⊤))))) =
      (# var_zero).
Proof. reflexivity. Qed.

(** A raw beta redex is neutral here, even though it is not beta-normal. *)

(** 原始 β 可归约式在这里是中性的，尽管它并非 β 正规形。 *)

Definition redex_is_raw_neutral
  : is_neutral_tm source_unit_redex
  := tt.

End Computations.
