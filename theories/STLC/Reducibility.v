From Cats.STLC Require Export ReductionRenaming.
From Cats.Set.Relation Require Export Candidate.

(** * Type-Indexed Reducibility

    Reducibility interprets a base or unit type by beta normalization, a
    product by reducibility of both projections, and a function by its
    action on reducible arguments in every renamed context. Future
    contexts allow a function to be tested at a fresh variable even when
    its original context has no variable of the required domain type.

    This relation is independent of NbE and uses the directed beta steps.
    Its candidate laws prove normalization of reducible terms, not yet
    reducibility of every typed term. The substitution fundamental theorem
    is the remaining bridge to that stronger statement. *)

(** * 按类型索引的可归约性

    可归约性以 β 强归一化解释基类型和单位类型，以两个投影的可归约性解释
    积类型，以在每个重命名后的上下文中将可归约实参送到可归约结果来解释
    函数类型。后续上下文允许用新变量测试函数，即使原上下文没有定义域类型
    的变量也可如此。

    此关系独立于 NbE，使用有向 β 步骤。候选律证明可归约项强归一化，尚未
    证明所有带类型项都可归约；替换基本定理是通向后一结论的剩余桥梁。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Interpretation and Renaming

    Fix syntax at [b], step evidence at [e], normalization trees at [s]
    and an independent step-classification bound [l]. Only [b <= e <= s]
    and [e < l] are required. In particular [s] may lie above or below [l].
    The interpretation is recursive on types and its witnesses remain
    transparent. Comparisons of terms use their native syntax equality. *)

(** ** 解释与重命名

    固定 [b] 处的语法、[e] 处的步骤证据、[s] 处的归一化树及独立步骤分类界
    [l]，只要求 [b <= e <= s] 和 [e < l]；[s] 可以高于或低于 [l]。
    解释按类型递归，其见证保持透明；项之间以原生语法相等比较。 *)

Section Reducibility.
Universes b e s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}}.

(** A reducible function acts in every renamed context; it need not carry
    equality or coherence proofs comparing these actions. They are syntax
    tests of one given term, rather than arbitrary semantic functions. *)

(** 可归约函数在每个重命名后的上下文中作用，不需要携带比较这些作用的相等或
    相干证明：这里是对一个给定项的语法测试，而非任意语义函数。 *)

Fixpoint Reducible (A : Ty B) (Γ : Ctx B)
  : Tm Γ A → Type@{s}
  := match A as U return Tm Γ U → Type@{s} with
  | ty_base _ | ty_unit => SN@{b e s} (@BetaStep@{b e l b} B Γ _)
  | ty_prod U V => λ t, Reducible U Γ (π₁ t) ∧ Reducible V Γ (π₂ t)
  | ty_arr U V => λ t, ∀ Δ (ρ : Ren@{b b} Δ Γ) (a : Tm Δ U),
      Reducible U Δ a → Reducible V Δ (t⟨ρ⟩ · a)
  end.

(** Native syntax equality gives equivalent reducibility evidence; no
    comparison of the witnesses themselves is required. *)

(** 原生语法相等给出等价的可归约性见证，不要求比较见证本身。 *)

Global Instance Reducible_proper (A : Ty B) (Γ : Ctx B)
  : Proper (eq ==> iffT) (Reducible A Γ).
Proof. intros t u h. subst u. exact ((λ p, p), (λ p, p)). Defined.

(** Reindexing preserves reducibility. At functions this simply composes
    the two renamings, with no equality of assignment functions. *)

(** 重索引保持可归约性；在函数处只需复合两个重命名，不要求赋值函数相等。 *)

Definition reducible_rename (A : Ty B)
  : ∀ Γ (t : Tm Γ A), Reducible A Γ t →
      ∀ Δ (ρ : Ren Δ Γ), Reducible A Δ t⟨ρ⟩.
Proof.
  induction A as [c | | A ihA U ihU | A ihA U ihU];
    intros Γ t p Δ ρ; cbn in *.
  - exact (sn_beta_rename p Δ ρ).
  - exact (sn_beta_rename p Δ ρ).
  - exact (ihA Γ (π₁ t) (fst p) Δ ρ,
      ihU Γ (π₂ t) (snd p) Δ ρ).
  - intros Θ τ a h. rewrite rename_comp. exact (p Θ (ρ ∘Ren τ) a h).
Defined.

(** Every directed beta reduct of a reducible term is reducible. The
    function case lifts a renamed function step into application. *)

(** 可归约项的每个有向 β 后继仍可归约；函数分支将重命名后的函数步骤提升到
    应用之下。 *)

Definition reducible_step (A : Ty B)
  : ∀ Γ (t u : Tm Γ A), BetaStep@{b e l b} t u →
      Reducible A Γ t → Reducible A Γ u.
Proof.
  induction A as [c | | A ihA U ihU | A ihA U ihU];
    intros Γ t u h p; cbn in *.
  - exact (sn_step p h).
  - exact (sn_step p h).
  - exact (ihA Γ (π₁ t) (π₁ u) (beta_step_lift op_fst h) (fst p),
      ihU Γ (π₂ t) (π₂ u) (beta_step_lift op_snd h) (snd p)).
  - intros Δ ρ a q. apply (ihU Δ (t⟨ρ⟩ · a) (u⟨ρ⟩ · a)).
    + exact (beta_step_lift (op_app_l a) (beta_step_rename h Δ ρ)).
    + exact (p Δ ρ a q).
Defined.

(** Normalization and neutral expansion are proved together by type
    induction. A function is tested at a fresh reducible variable; neutral
    function expansion uses induction on the argument's normalization
    tree. Step reflection handles the renamed head's reducts. *)

(** 强归一化与中性展开按类型同时归纳证明。函数用新鲜可归约变量测试；中性
    函数展开对实参的归一化树归纳，步骤反射则处理重命名后头部的后继。 *)

Definition reducible_candidate_laws (A : Ty B)
  : (∀ Γ (t : Tm Γ A), Reducible A Γ t →
      SN@{b e s} (@BetaStep@{b e l b} B Γ A) t) ∧
    (∀ Γ, is_neutral_expansion@{b e s l _ _} (Reducible A Γ)).
Proof.
  induction A as [c | | A [snA expandA] U [snU expandU] |
    A [snA expandA] U [snU expandU]].
  - split; [exact (λ Γ t p, p) |].
    intros Γ t n next. exact (sn_intro next).
  - split; [exact (λ Γ t p, p) |].
    intros Γ t n next. exact (sn_intro next).
  - split.
    + intros Γ t p.
      exact (sn_simulation (λ u, π₁ u)
        (λ u v h, beta_step_lift op_fst h) t (snA Γ (π₁ t) (fst p))).
    + intros Γ t n next. split.
      * apply (expandA Γ); [exact tt |]. intros v h.
        destruct (beta_step_fst_inv h) as [r | [u [k z]]].
        -- exact (match root_beta_intro_source r n with end).
        -- subst v. exact (fst (next u k)).
      * apply (expandU Γ); [exact tt |]. intros v h.
        destruct (beta_step_snd_inv h) as [r | [u [k z]]].
        -- exact (match root_beta_intro_source r n with end).
        -- subst v. exact (snd (next u k)).
  - split.
    + intros Γ t p.
      pose (a := neutral_expansion_var (expandA (Γ ▻ A)) var_zero).
      pose (q := snU (Γ ▻ A) (t⟨wkRen⟩ · (# var_zero))
        (p (Γ ▻ A) wkRen (# var_zero) a)).
      exact (sn_simulation (λ u, u⟨wkRen⟩ · (# var_zero))
        (λ u v h, beta_step_lift (op_app_l (# var_zero))
          (beta_step_rename h (Γ ▻ A) wkRen)) t q).
    + intros Γ t n next Δ ρ a ra.
      assert (go : ∀ u, SN@{b e s} (@BetaStep@{b e l b} B Δ A) u →
        Reducible A Δ u → Reducible U Δ (t⟨ρ⟩ · u)).
      { intros u p. induction p as [u children ih]. intros ru.
        apply (expandU Δ); [exact tt |]. intros v h.
        destruct (beta_step_app_inv h) as
          [r | [[f [k z]] | [a' [k z]]]].
        - exact (match root_beta_intro_source r
            (snd (neutral_tm_rename t ρ) n) with end).
        - subst v.
          destruct (beta_step_rename_inv t Δ ρ f k) as [f' [p z]].
          subst f. exact (next f' p Δ ρ u ru).
        - subst v. exact (ih a' k (reducible_step A Δ u a' k ru)). }
      exact (go a (snA Δ a ra) ra).
Defined.

(** Reducible terms have trees covering all beta paths. *)

(** 可归约项具有覆盖全部 β 路径的归一化树。 *)

Definition reducible_sn (A : Ty B) (Γ : Ctx B) (t : Tm Γ A)
  : Reducible A Γ t → SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := fst (reducible_candidate_laws A) Γ t.

(** The concrete reducibility predicate satisfies the general neutral
    expansion interface; it is no longer merely an assumed law. *)

(** 具体可归约性谓词满足一般中性展开接口；这里已是证明，而非仅假设此律。 *)

Definition reducible_expand (A : Ty B) (Γ : Ctx B)
  : is_neutral_expansion@{b e s l _ _} (Reducible A Γ)
  := snd (reducible_candidate_laws A) Γ.

(** Package the three proven laws using the relation-independent
    candidate interface. This is a property instance, not a chosen model. *)

(** 用不依赖具体关系的候选接口组装已证的三条律；这是性质实例，不是选定模型。 *)

Global Instance Reducible_IsReducibilityCandidate (A : Ty B) (Γ : Ctx B)
  : IsReducibilityCandidate (@BetaStep@{b e l b} B Γ A)
      (@is_neutral_tm B Γ A) (Reducible A Γ).
Proof.
  refine {|candidate_sn := reducible_sn A Γ
          ; candidate_step := reducible_step A Γ
          ; candidate_expand := reducible_expand A Γ
          |}.
Defined.

(** Every variable is reducible, including the fresh function test. *)

(** 每个变量都可归约，包括用于测试函数的新变量。 *)

Definition reducible_var (A : Ty B) (Γ : Ctx B) (x : Var Γ A)
  : Reducible A Γ (# x)
  := neutral_expansion_var (reducible_expand A Γ) x.

End Reducibility.
