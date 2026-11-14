From Cats.STLC Require Export ReductionRenaming.
From Cats.Set.Relation Require Export Candidate.

(** * Beta Expansion in Reducibility Candidates

    Candidate step closure transports membership forwards. The converse
    needs more care: a beta redex may reduce inside a component that root
    contraction would discard. Normalization of these components and
    neutral expansion recover membership of the redex from its contractum.

    Work with any candidate on the result type, independently of the
    concrete type-indexed reducibility interpretation. Nested normalization
    induction covers steps in both components; root uniqueness identifies
    the contractum without injecting dependent syntax constructors. *)

(** * 可归约性候选中的 β 展开

    候选的步骤封闭性向前传递成员性。反方向需要额外注意：β 可归约式可以先在
    根收缩将丢弃的分量内部归约。结合这些分量的强归一化与中性展开，才能从
    收缩结果的成员性恢复整个可归约式的成员性。

    在结果类型的任意候选上工作，独立于具体的逐类型可归约性解释。嵌套归一化
    归纳覆盖两个分量的步骤；根唯一性识别收缩结果，不对依赖语法构造器作单射
    消去。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_sub_scope.

(** ** Pulling Normalization Back through Substitution

    Fix independent syntax, step and tree bounds. Every original beta
    step is preserved by substitution, so a normalization tree at a
    substituted term pulls back along that simulation. No injectivity of
    the assignment is required, and no preservation in the other direction
    is assumed here. *)

(** ** 经替换拉回归一化

    固定独立的语法、步骤及树大小界。替换保持每个原 β 步骤，因此替换结果处
    的归一化树可沿此模拟拉回。不要求赋值单射，这里也不假设另一方向的保持性。 *)

Section SubstitutionNormalization.
Universes b e s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** Normalization of a substituted instance implies normalization of the
    original term, by the general simulation pullback. *)

(** 一般模拟拉回表明，替换实例强归一化蕴含原项强归一化。 *)

Definition sn_beta_subst_inv (t : Tm Γ A) (σ : Sub Δ Γ)
    (p : SN@{b e s} (@BetaStep@{b e l b} B Δ A) t[σ])
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := sn_simulation (λ u, u[σ])
      (λ u v h, beta_step_subst h Δ σ) t p.

End SubstitutionNormalization.

(** ** Expansion for an Arbitrary Candidate

    Fix a context, result type and candidate [P]. Membership lives at [p],
    trees at [s], and candidate laws at [k]; these remain distinct from
    step evidence [e] and relation classification [l]. The discarded
    component's normalization is explicit in each projection law.
    Function expansion needs normalization of the argument; normalization
    of the body follows by simulation from the candidate contractum. *)

(** ** 任意候选的展开

    固定上下文、结果类型与候选 [P]。成员性位于 [p]、树位于 [s]、候选律位于
    [k]；它们与步骤证据 [e] 及关系分类界 [l] 保持区分。每条投影律都显式要求
    被丢弃分量强归一化。函数展开要求实参强归一化；项体的强归一化则由候选中
    的收缩结果经模拟拉回取得。 *)

Section CandidateExpansion.
Universes b e p s l k.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {U : Ty B}.
Context (P : Tm Γ U → Type@{p}).
Context (hP : IsReducibilityCandidate@{b e Set p s k}
  (@BetaStep@{b e l b} B Γ U) (@is_neutral_tm B Γ U) P).

(** The first projection expands when its selected component belongs to
    the candidate and its discarded component is strongly normalizing. *)

(** 所选分量属于候选且丢弃分量强归一化时，第一投影可以展开。 *)

Definition candidate_fst_pair {A : Ty B} (t : Tm Γ U) (u : Tm Γ A)
    (ht : P t) (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u)
  : P (π₁ ⟨t, u⟩).
Proof.
  refine (sn_pair_induction (λ t u, P t → P (π₁ ⟨t, u⟩)) _
    (@candidate_sn _ _ _ _ hP t ht) hu ht).
  intros a c ihA ihC pa.
  apply (@candidate_expand _ _ _ _ hP); [exact tt |]. intros v h.
  destruct (beta_step_fst_inv h) as [r | [q [k z]]].
  - pose proof (root_beta_unique r (root_beta_fst a c)) as z.
    subst v. exact pa.
  - destruct (beta_step_pair_inv k) as [[a' [h' z']] | [c' [h' z']]];
      subst q; subst v.
    + exact (ihA a' h' (@candidate_step _ _ _ _ hP a a' h' pa)).
    + exact (ihC c' h' pa).
Defined.

(** The second projection has the corresponding explicit normalization
    requirement on its discarded first component. *)

(** 第二投影对应地显式要求被丢弃的第一分量强归一化。 *)

Definition candidate_snd_pair {A : Ty B} (t : Tm Γ A) (u : Tm Γ U)
    (ht : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t) (hu : P u)
  : P (π₂ ⟨t, u⟩).
Proof.
  refine (sn_pair_induction (λ t u, P u → P (π₂ ⟨t, u⟩)) _
    ht (@candidate_sn _ _ _ _ hP u hu) hu).
  intros a c ihA ihC pc.
  apply (@candidate_expand _ _ _ _ hP); [exact tt |]. intros v h.
  destruct (beta_step_snd_inv h) as [r | [q [k z]]].
  - pose proof (root_beta_unique r (root_beta_snd a c)) as z.
    subst v. exact pc.
  - destruct (beta_step_pair_inv k) as [[a' [h' z']] | [c' [h' z']]];
      subst q; subst v.
    + exact (ihA a' h' pc).
    + exact (ihC c' h' (@candidate_step _ _ _ _ hP c c' h' pc)).
Defined.

(** Beta expansion accounts for reductions of the body and argument.
    Changing the body preserves a single step after substitution; changing
    the argument may duplicate or discard steps, so it uses a finite path.
    Argument normalization is required even when the body ignores it. *)

(** β 展开覆盖项体和实参的归约。改变项体经过替换后仍保持一步；改变实参
    可能复制或丢弃步骤，因而使用有限路径。即使项体忽略实参，也要求实参强
    归一化。 *)

Definition candidate_beta_function {A : Ty B} (t : Tm (Γ ▻ A) U)
    (u : Tm Γ A) (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u)
    (ht : P t[u/])
  : P ((ƛ t) · u).
Proof.
  pose (st := sn_beta_subst_inv t (sub_single u)
    (@candidate_sn _ _ _ _ hP t[u/] ht)).
  refine (sn_pair_induction (λ t u, P t[u/] → P ((ƛ t) · u)) _ st hu ht).
  intros a c ihA ihC pc.
  apply (@candidate_expand _ _ _ _ hP); [exact tt |]. intros v h.
  destruct (beta_step_app_inv h) as [r | [[f [k z]] | [c' [k z]]]].
  - pose proof (root_beta_unique r (root_beta_function a c)) as z.
    subst v. exact pc.
  - destruct (beta_step_lam_inv k) as [a' [h' z']]. subst f. subst v.
    exact (ihA a' h' (@candidate_step _ _ _ _ hP _ _
      (beta_step_subst h' Γ (sub_single c)) pc)).
  - subst v. exact (ihC c' k
      (candidate_rtc hP (beta_rtc_single a (rtc_step k)) pc)).
Defined.

End CandidateExpansion.
