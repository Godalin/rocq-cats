From Cats.STLC Require Export
  Reducibility
  ReductionExpansion.

(** * Reducible Term Constructors

    Introductions must satisfy every elimination test in their type's
    interpretation. Pair reducibility therefore uses both projection
    expansion laws. Lambda reducibility uses function beta expansion in
    each future context. The discarded components are normalizing because
    they are reducible; no termination claim about all terms is used here.

    Elimination lemmas unpack the interpretation. They make the subsequent
    syntax induction readable without duplicating candidate arguments. *)

(** * 可归约项的构造器

    引入形式必须满足其类型解释中的每个消去测试，因此配对可归约性使用两条
    投影展开律，λ 可归约性在每个后续上下文中使用函数 β 展开。丢弃分量因其
    可归约而强归一化；这里不使用所有项终止的结论。

    消去引理直接展开解释，使后续语法归纳清晰，而不重复候选论证。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Introduction and Elimination Laws

    Fix arbitrary labels, a context, and separate syntax [b], step [e],
    tree [s] and classification [l] bounds. Lambda's premise ranges over
    renamed contexts and reducible arguments. It concerns substituted
    bodies, not equality of functions or a chosen evaluation strategy. *)

(** ** 引入与消去律

    固定任意标签、上下文及相互区分的语法界 [b]、步骤界 [e]、树界 [s] 和分类
    界 [l]。λ 的前提对重命名后的上下文与可归约实参量化；它讨论替换后的
    项体，不要求函数相等，也不指定求值策略。 *)

Section Constructors.
Universes b e s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}} {Γ : Ctx B}.

(** Unit is reducible because it has no outgoing beta steps. *)

(** 单位没有向外 β 步骤，因而可归约。 *)

Definition reducible_unit
  : Reducible@{b e s l} ⊤ Γ ⋆
  := sn_terminal (λ u h, beta_step_unit_absurd h).

(** Reducible components pass both elimination tests of the pair. Each
    projection expansion uses normalization of the unselected component. *)

(** 可归约分量通过配对的两个消去测试；每条投影展开都使用未选分量的强归一化。 *)

Definition reducible_pair {A U : Ty B} {t : Tm Γ A} {u : Tm Γ U}
    (ht : Reducible@{b e s l} A Γ t) (hu : Reducible@{b e s l} U Γ u)
  : Reducible@{b e s l} (A × U) Γ (⟨t, u⟩).
Proof.
  split.
  - exact (candidate_fst_pair (Reducible A Γ)
      (Reducible_IsReducibilityCandidate A Γ) t u ht
      (reducible_sn U Γ u hu)).
  - exact (candidate_snd_pair (Reducible U Γ)
      (Reducible_IsReducibilityCandidate U Γ) t u
      (reducible_sn A Γ t ht) hu).
Defined.

(** Product reducibility already contains its first projection test. *)

(** 积可归约性已经包含第一投影测试。 *)

Definition reducible_fst {A U : Ty B} {t : Tm Γ (A × U)}
    (h : Reducible@{b e s l} (A × U) Γ t)
  : Reducible@{b e s l} A Γ (π₁ t)
  := fst h.

(** The second projection is the other test. *)

(** 第二投影是另一个测试。 *)

Definition reducible_snd {A U : Ty B} {t : Tm Γ (A × U)}
    (h : Reducible@{b e s l} (A × U) Γ t)
  : Reducible@{b e s l} U Γ (π₂ t)
  := snd h.

(** Test a function in its present context using identity renaming. *)

(** 用恒等重命名在当前上下文中测试函数。 *)

Definition reducible_app {A U : Ty B} {f : Tm Γ (A ⇒ U)} {a : Tm Γ A}
    (hf : Reducible@{b e s l} (A ⇒ U) Γ f)
    (ha : Reducible@{b e s l} A Γ a)
  : Reducible@{b e s l} U Γ (f · a).
Proof.
  pose proof (hf Γ idRen a ha) as h. now rewrite rename_id in h.
Defined.

(** If every renamed body with a reducible argument substituted is
    reducible, the abstraction is reducible. Argument normalization and
    the contractum suffice for candidate beta expansion; no separate
    normalization assumption on the body is needed. *)

(** 若每个重命名后的项体代入可归约实参后都可归约，则抽象可归约。实参的强
    归一化和收缩结果足以使用候选 β 展开，无须单独假设项体强归一化。 *)

Definition reducible_lam {A U : Ty B} (t : Tm (Γ ▻ A) U)
    (ht : ∀ Δ (ρ : Ren Δ Γ) (u : Tm Δ A),
      Reducible@{b e s l} A Δ u →
      Reducible@{b e s l} U Δ t⟨ρ^↑Ren⟩[u/])
  : Reducible@{b e s l} (A ⇒ U) Γ (ƛ t).
Proof.
  intros Δ ρ u hu.
  exact (candidate_beta_function (Reducible U Δ)
    (Reducible_IsReducibilityCandidate U Δ) t⟨ρ^↑Ren⟩ u
    (reducible_sn A Δ u hu) (ht Δ ρ u hu)).
Defined.

End Constructors.
