From Cats.STLC Require Export Reduction.
From Cats.Set.Relation Require Import Compatible.

(** * Reading the Source of a Beta Step

    The existing reduction is the compatible closure of root beta. To use
    a step in a normalization argument, we also need to know which part of
    its source changed. Define that information by matching on the typed
    source, then obtain it by the general compatible-closure fold.

    No constructor-injection principle for dependent syntax is assumed.
    The analysis keeps all child-step witnesses and reconstructs the
    target by native syntax equality. Elimination forms retain a root
    witness as an additional alternative. *)

(** * 读取 β 步骤的来源

    现有归约是根 β 的相容闭包。为了在归一化论证中使用一个步骤，还需要知道
    其源项的哪一部分发生变化。先对带类型源项作模式匹配来定义这些信息，再用
    一般相容闭包折叠取得它们。

    不假设依赖语法的构造器单射原则。分析保留全部子步骤见证，并按原生语法
    相等重构目标；消去形式还保留根步骤见证这一备选分支。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Source-Indexed Analysis

    Fix a signature at [b], step evidence at [e] with [b <= e], and an
    auxiliary relation-classification bound [l] above [e]. The analysis
    itself stays in [Type@{e}]. Its cases depend on the source constructor,
    so variables and unit have no case, while a pair or lambda can only
    change a child. *)

(** ** 以源项为索引的分析

    固定 [b] 处的签名、满足 [b <= e] 的步骤证据界 [e]，以及高于 [e] 的关系
    分类辅助界 [l]。分析本身仍位于 [Type@{e}]。其分支取决于源构造器：变量
    与单位没有分支，配对或 λ 只能改变子项。 *)

Section SourceAnalysis.
Universes b e l.
Constraint b <= e, e < l.
Context {B : Type@{b}}.

(** All possibilities for one step, indexed by its actual source. Each
    contextual case changes exactly one child and retains the other data. *)

(** 按实际源项索引的一步全部可能性；每个上下文分支恰好改变一个子项，保留
    其余数据。 *)

Definition BetaSource {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type@{e}
  := match t in Tm Γ A return Tm Γ A → Type@{e} with
  | tm_var _ => λ _, Empty_set
  | tm_unit => λ _, Empty_set
  | tm_pair p q => λ v,
      (∃ p', BetaStep@{b e l b} p p' ∧ v = ⟨p', q⟩) ∨
      (∃ q', BetaStep@{b e l b} q q' ∧ v = ⟨p, q'⟩)
  | tm_fst p => λ v,
      RootBeta@{b e b} (π₁ p) v ∨
      (∃ p', BetaStep@{b e l b} p p' ∧ v = π₁ p')
  | tm_snd p => λ v,
      RootBeta@{b e b} (π₂ p) v ∨
      (∃ p', BetaStep@{b e l b} p p' ∧ v = π₂ p')
  | tm_lam p => λ v,
      ∃ p', BetaStep@{b e l b} p p' ∧ v = ƛ p'
  | tm_app f a => λ v,
      RootBeta@{b e b} (f · a) v ∨
      ((∃ f', BetaStep@{b e l b} f f' ∧ v = f' · a) ∨
       (∃ a', BetaStep@{b e l b} a a' ∧ v = f · a'))
  end u.

(** A root step supplies the root alternative of an elimination form. *)

(** 根步骤提供消去形式中的根分支。 *)

Definition root_beta_source {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootBeta@{b e b} t u)
  : BetaSource t u.
Proof. destruct h; cbn; left; constructor. Defined.

(** Retain the child step alongside its analysis. This paired target is
    compatible, because an enclosing constructor needs exactly that child
    witness to describe where its own step occurred. *)

(** 将子步骤与其分析一起保留。这个配对目标相容，因为外层构造器恰好需要该
    子步骤见证来说明自身步骤发生的位置。 *)

Definition beta_source_compatible
  : is_compatible (TmContexts B)
      (λ i t u, ContextStep (@RootBeta@{b e b} B) t u ∧
        BetaSource t u).
Proof.
  intros [Γ A] [Δ U] c t u [p q]. split.
  - exact (context_step_lift (@RootBeta@{b e b} B) c p).
  - destruct c; cbn.
    + exact (inl (existT _ u (p, eq_refl))).
    + exact (inr (existT _ u (p, eq_refl))).
    + exact (inr (existT _ u (p, eq_refl))).
    + exact (inr (existT _ u (p, eq_refl))).
    + exact (existT _ u (p, eq_refl)).
    + exact (inr (inl (existT _ u (p, eq_refl)))).
    + exact (inr (inr (existT _ u (p, eq_refl)))).
Defined.

(** Fold the original contextual derivation into its source analysis.
    This does not inspect or identify arbitrary equality proofs of indices. *)

(** 将原上下文推导折叠为源项分析，不检查或识别索引的任意相等证明。 *)

Definition beta_step_source {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : BetaStep@{b e l b} t u)
  : BetaSource t u
  := snd (context_closure_preserves (TmContexts B)
      beta_source_compatible
      (λ i x y p,
        (context_step_root _ p, root_beta_source p))
      (Γ, A) t u h).

(** Reconstruct the contextual step from any source-analysis case. Native
    target equations only substitute within the already fixed judgement. *)

(** 从任意源分析分支重构上下文步骤。原生目标等式只在已经固定的判断内代换。 *)

Definition beta_source_step {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : BetaSource t u → BetaStep@{b e l b} t u.
Proof.
  destruct t as [Γ0 A0 x | Γ0 | Γ0 A0 U p q | Γ0 A0 U p |
    Γ0 A0 U p | Γ0 A0 U p | Γ0 A0 U f a]; cbn; intros h.
  - destruct h.
  - destruct h.
  - destruct h as [[v [h z]] | [v [h z]]]; subst u.
    + exact (context_step_lift _ (op_pair_l q) h).
    + exact (context_step_lift _ (op_pair_r p) h).
  - destruct h as [h | [v [h z]]].
    + exact (context_step_root _ h).
    + subst u. exact (context_step_lift _ op_fst h).
  - destruct h as [h | [v [h z]]].
    + exact (context_step_root _ h).
    + subst u. exact (context_step_lift _ op_snd h).
  - destruct h as [v [h z]]. subst u.
    exact (context_step_lift _ op_lam h).
  - destruct h as [h | [[v [h z]] | [v [h z]]]].
    + exact (context_step_root _ h).
    + subst u. exact (context_step_lift _ (op_app_l a) h).
    + subst u. exact (context_step_lift _ (op_app_r f) h).
Defined.

(** The source view and original step supply maps in both directions.
    No inverse equations on derivations or equality witnesses are asserted. *)

(** 源视图与原步骤之间有双向映射，不断言推导或相等见证上的互逆方程。 *)

Definition beta_step_source_iff {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : BetaStep@{b e l b} t u ↔ BetaSource t u
  := (beta_step_source, beta_source_step t u).

(** Variables have no root or child beta step. *)

(** 变量没有根 β 步骤或子步骤。 *)

Definition beta_step_var_absurd {Γ : Ctx B} {A : Ty B}
    (x : Var Γ A) {u : Tm Γ A} (h : BetaStep@{b e l b} (# x) u)
  : Empty_set
  := beta_step_source h.

(** Unit has no beta step; its separate eta equation is not involved. *)

(** 单位没有 β 步骤；其独立的 η 方程不参与此结论。 *)

Definition beta_step_unit_absurd {Γ : Ctx B} {u : Tm Γ ⊤}
    (h : BetaStep@{b e l b} ⋆ u)
  : Empty_set
  := beta_step_source h.

(** A pair step reduces exactly one component, leaving the other fixed. *)

(** 配对的一步恰好归约一个分量，另一个保持不变。 *)

Definition beta_step_pair_inv {Γ : Ctx B} {A U : Ty B}
    {p : Tm Γ A} {q : Tm Γ U} {u : Tm Γ (A × U)}
    (h : BetaStep@{b e l b} (⟨p, q⟩) u)
  : (∃ p', BetaStep@{b e l b} p p' ∧ u = ⟨p', q⟩) ∨
    (∃ q', BetaStep@{b e l b} q q' ∧ u = ⟨p, q'⟩)
  := beta_step_source h.

(** An abstraction step comes from a body step in its extended context. *)

(** 抽象的一步来自扩张上下文中的项体步骤。 *)

Definition beta_step_lam_inv {Γ : Ctx B} {A U : Ty B}
    {p : Tm (Γ ▻ A) U} {u : Tm Γ (A ⇒ U)}
    (h : BetaStep@{b e l b} (ƛ p) u)
  : ∃ p', BetaStep@{b e l b} p p' ∧ u = ƛ p'
  := beta_step_source h.

(** First projection either contracts at the root or reduces its input. *)

(** 第一投影或者在根部收缩，或者归约其输入。 *)

Definition beta_step_fst_inv {Γ : Ctx B} {A U : Ty B}
    {p : Tm Γ (A × U)} {u : Tm Γ A}
    (h : BetaStep@{b e l b} (π₁ p) u)
  : RootBeta@{b e b} (π₁ p) u ∨
    (∃ p', BetaStep@{b e l b} p p' ∧ u = π₁ p')
  := beta_step_source h.

(** Second projection has the corresponding two alternatives. *)

(** 第二投影具有对应的两种备选。 *)

Definition beta_step_snd_inv {Γ : Ctx B} {A U : Ty B}
    {p : Tm Γ (A × U)} {u : Tm Γ U}
    (h : BetaStep@{b e l b} (π₂ p) u)
  : RootBeta@{b e b} (π₂ p) u ∨
    (∃ p', BetaStep@{b e l b} p p' ∧ u = π₂ p')
  := beta_step_source h.

(** Application exposes root contraction, function reduction or argument
    reduction. The hidden domain remains the domain of the given source. *)

(** 应用暴露根收缩、函数归约或实参归约；隐藏的定义域仍是所给源项的定义域。 *)

Definition beta_step_app_inv {Γ : Ctx B} {A U : Ty B}
    {f : Tm Γ (A ⇒ U)} {a : Tm Γ A} {u : Tm Γ U}
    (h : BetaStep@{b e l b} (f · a) u)
  : RootBeta@{b e b} (f · a) u ∨
    ((∃ f', BetaStep@{b e l b} f f' ∧ u = f' · a) ∨
     (∃ a', BetaStep@{b e l b} a a' ∧ u = f · a'))
  := beta_step_source h.

End SourceAnalysis.

(** ** Neutral Raw Terms

    Fix an arbitrary signature. For reducibility arguments, a raw neutral
    is a variable or an elimination form, including a beta redex. It need
    not be a normal neutral from the NbE syntax. Unit, pairs and lambdas
    are introductions and have no neutral witness here.

    This predicate only inspects the outer constructor. Renaming preserves
    it in both directions; substitution need not, since it may replace a
    variable by an introduction. No termination or candidate-expansion
    theorem is assumed by introducing this predicate. *)

(** ** 中性原始项

    固定任意签名。可归约性论证中的原始中性项是变量或消去形式，包括 β 可
    归约式，不要求它是 NbE 语法中的正规中性项。单位、配对和 λ 是引入形式，
    在这里没有中性见证。

    此谓词只检查最外层构造器。重命名双向保持它，但替换未必保持，因为替换
    可以用引入形式代替变量。引入此谓词并不假设终止性或候选展开定理。 *)

Section NeutralTerms.
Context {B : Type}.

(** A Type-valued test for a variable or elimination at the outermost node. *)

(** 最外层节点为变量或消去形式的 Type 值判别。 *)

Definition is_neutral_tm {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : Type
  := match t with
  | tm_var _ | tm_fst _ | tm_snd _ | tm_app _ _ => unit
  | tm_unit | tm_pair _ _ | tm_lam _ => Empty_set
  end.

(** Renaming changes variables but preserves the outer constructor. *)

(** 重命名改变变量，但保持最外层构造器。 *)

Definition neutral_tm_rename {Γ Δ : Ctx B} {A : Ty B}
    (t : Tm Γ A) (ρ : Ren Δ Γ)
  : is_neutral_tm t⟨ρ⟩ ↔ is_neutral_tm t.
Proof. destruct t; exact ((λ h, h), (λ h, h)). Defined.

End NeutralTerms.

(** A root beta contraction always has an elimination form as its source,
    hence a neutral raw term in the sense just defined. *)

(** 根 β 收缩的源始终是消去形式，因而是刚定义的原始中性项。 *)

Definition root_beta_neutral@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : RootBeta@{b e _} t u)
  : is_neutral_tm t.
Proof. destruct h; exact tt. Defined.

(** ** Using a Neutral-Expansion Law

    Fix a context and result type, step evidence at [e], and a predicate
    [P] with an independent result universe [p]. Neutral expansion is an
    explicit hypothesis on [P], not a theorem about arbitrary predicates.
    The source inversions above reduce its use to the possible root and
    child cases. No normalization hypothesis is needed for these wrappers. *)

(** ** 使用中性展开律

    固定上下文与结果类型、[e] 处的步骤证据，以及结果宇宙 [p] 独立的谓词
    [P]。中性展开是 [P] 的显式假设，不是任意谓词都满足的定理。上面的源反演
    将它的使用化为可能的根分支与子项分支。这些封装不需要归一化假设。 *)

Section NeutralExpansion.
Universes b e p l.
Constraint b <= e, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** A predicate admits neutral expansion when it holds at a neutral term
    whenever it holds at every one-step reduct of that term. The law uses
    an auxiliary universe containing its quantified data. *)

(** 若谓词在一个中性项的每个一步后继处成立时，也在该项处成立，就称它允许
    中性展开。此律另用容纳其量化数据的辅助宇宙。 *)

Definition is_neutral_expansion (P : Tm Γ A → Type@{p})
  : Type
  := ∀ t, is_neutral_tm t →
      (∀ u, BetaStep@{b e l b} t u → P u) → P t.

(** Pointwise equivalent predicates have equivalent expansion laws. The
    comparison transforms witnesses rather than equating predicates. *)

(** 逐点等价的谓词具有等价的展开律；比较转换见证，而不要求谓词相等。 *)

Global Instance is_neutral_expansion_proper
  : Proper (pointwise_relation (Tm Γ A) iffT ==> iffT)
      is_neutral_expansion.
Proof.
  intros P Q h. split; intros hp t n next.
  - exact (fst (h t)
      (hp t n (λ u r, snd (h u) (next u r)))).
  - exact (snd (h t)
      (hp t n (λ u r, fst (h u) (next u r)))).
Defined.

(** Variables satisfy any neutrally expanding predicate, because they
    have no beta reducts. *)

(** 变量没有 β 后继，因此满足任何允许中性展开的谓词。 *)

Definition neutral_expansion_var {P : Tm Γ A → Type@{p}}
    (hp : is_neutral_expansion P) (x : Var Γ A)
  : P (# x)
  := hp (# x) tt (λ u h, match beta_step_var_absurd x h with end).

(** Expanding a first projection requires the root and input-step cases.
    Target reconstruction is handled by native equality elimination. *)

(** 展开第一投影需要根分支与输入步骤分支；目标重构通过原生相等消去处理。 *)

Definition neutral_expansion_fst {P : Tm Γ A → Type@{p}}
    (hp : is_neutral_expansion P) {U : Ty B} (t : Tm Γ (A × U))
    (hr : ∀ u, RootBeta@{b e b} (π₁ t) u → P u)
    (hc : ∀ t', BetaStep@{b e l b} t t' → P (π₁ t'))
  : P (π₁ t).
Proof.
  apply hp; [exact tt |]. intros u h.
  destruct (beta_step_fst_inv h) as [r | [t' [k z]]].
  - exact (hr u r).
  - subst u. exact (hc t' k).
Defined.

(** Second projection has the same two proof obligations. *)

(** 第二投影具有同样的两个证明义务。 *)

Definition neutral_expansion_snd {P : Tm Γ A → Type@{p}}
    (hp : is_neutral_expansion P) {U : Ty B} (t : Tm Γ (U × A))
    (hr : ∀ u, RootBeta@{b e b} (π₂ t) u → P u)
    (hc : ∀ t', BetaStep@{b e l b} t t' → P (π₂ t'))
  : P (π₂ t).
Proof.
  apply hp; [exact tt |]. intros u h.
  destruct (beta_step_snd_inv h) as [r | [t' [k z]]].
  - exact (hr u r).
  - subst u. exact (hc t' k).
Defined.

(** Expanding an application requires all three possible step sources:
    root contraction, a function step and an argument step. *)

(** 展开应用需要全部三种步骤来源：根收缩、函数步骤与实参步骤。 *)

Definition neutral_expansion_app {P : Tm Γ A → Type@{p}}
    (hp : is_neutral_expansion P) {U : Ty B}
    (f : Tm Γ (U ⇒ A)) (a : Tm Γ U)
    (hr : ∀ u, RootBeta@{b e b} (f · a) u → P u)
    (hf : ∀ f', BetaStep@{b e l b} f f' → P (f' · a))
    (ha : ∀ a', BetaStep@{b e l b} a a' → P (f · a'))
  : P (f · a).
Proof.
  apply hp; [exact tt |]. intros u h.
  destruct (beta_step_app_inv h) as [r | [[f' [k z]] | [a' [k z]]]].
  - exact (hr u r).
  - subst u. exact (hf f' k).
  - subst u. exact (ha a' k).
Defined.

End NeutralExpansion.
