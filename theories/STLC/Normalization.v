From Cats Require Export STLC.Evaluation.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Kripke.

(** * Normalization by Evaluation

    To normalize an open term, reflect its free variables into a semantic
    environment, evaluate the term, then reify the resulting value. All
    three operations are transparent, so this defines an executable map
    from arbitrary typed terms to beta-normal, eta-long syntax trees.

    Termination here is structural recursion in the metatheory. It is not
    a claim about every directed reduction sequence. Likewise, producing
    a well-shaped normal tree alone does not prove beta/eta equality with
    its input: full soundness and invariance require further arguments. *)

(** * 通过求值正规化

    正规化开放项时，先将自由变量反射到语义环境，再求值该项，最后实化所得
    语义值。三个操作均透明，因此定义了从任意带类型项到 β 正规、η 长语法树
    的可执行映射。

    此处终止性来自元理论中的结构递归，并不是关于每条有向归约序列的断言。
    同样，仅产生形状正确的正规树尚不能证明其与输入 βη 相等；完整可靠性与
    不变性需要进一步论证。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** Reflect a renamed collection of free variables. Recursion follows
    the source context; the target world remains fixed. This more general
    environment makes the context coherence of initialization explicit. *)

(** 反射经重命名的一组自由变量。递归沿源上下文进行，目标世界保持不变。
    此更一般的环境使初始化的上下文相容性能够显式陈述。 *)

Fixpoint reflected_env@{b r s l +} {B : Type@{b}} (Γ : Ctx B)
  : ∀ Δ : Ctx B, Ren Δ Γ →
      EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Δ.
Proof.
  destruct Γ as [| Γ A]; intros Δ ρ.
  - exact tt.
  - exact (reflected_env B Γ Δ (λ U x, ρ U (var_succ x)),
      reflect_ne (TypeReification@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A) Δ
        (ne_var (ρ A var_zero))).
Defined.

(** Lookup recovers precisely the reflected variable at its renamed
    position. This law needs neither equality of labels nor proof fields. *)

(** 查找恰好恢复重命名位置处的反射变量，不比较标签或证明字段的相等。 *)

Lemma reflected_env_lookup@{b r s l +} {B : Type@{b}} (Γ : Ctx B)
  : ∀ (Δ : Ctx B) (ρ : Ren Δ Γ) (A : Ty B) (x : Var Γ A),
      EnvLookupN Γ A x Δ (reflected_env@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Δ ρ) ≈S
        reflect_ne (TypeReification@{b r s l
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A) Δ
          (ne_var (ρ A x)).
Proof.
  induction Γ as [| Γ IH U]; intros Δ ρ A x.
  - destruct x.
  - destruct x as [x | x].
    + exact (IH Δ (λ T y, ρ T (var_succ y)) A x).
    + destruct x. reflexivity.
Defined.

(** Pointwise equal renamings produce equivalent environments. *)

(** 逐点相等的重命名产生等价环境。 *)

Global Instance reflected_env_proper@{b r s l +} {B : Type@{b}} (Γ Δ : Ctx B)
  : Proper (RenEq ==> [≈S]) (reflected_env@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Δ).
Proof.
  induction Γ as [| Γ IH A]; intros ρ τ h.
  - exact tt.
  - split.
    + apply IH. intros U x. apply h.
    + apply reflect_ne_proper. f_equal. apply h.
Defined.

(** Reindexing the initialized values agrees with composing the supplied
    renaming. Reflection's naturality is used at each context declaration. *)

(** 重索引初始化后的值，等于复合所给重命名；在上下文每个声明处使用反射的
    自然性。 *)

Lemma reflected_env_reindex@{b r s l +} {B : Type@{b}} (Γ : Ctx B)
  : ∀ (Δ Θ : Ctx B) (ρ : Ren Δ Γ) (τ : Ren Θ Δ),
      fmap (EnvF Γ) τ (reflected_env@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Δ ρ) ≈S
        reflected_env Γ Θ (ρ ∘Ren τ).
Proof.
  induction Γ as [| Γ IH A]; intros Δ Θ ρ τ.
  - exact tt.
  - split.
    + exact (IH Δ Θ (λ U x, ρ U (var_succ x)) τ).
    + exact (reflect_ne_rename (TypeReification@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A) Δ Θ τ
        (ne_var (ρ A var_zero))).
Defined.

(** Selecting reflected entries composes their renamings. In particular,
    selecting an initial environment reflects the selected variables. *)

(** 选取反射后的分量会复合其重命名。特别地，选取初始环境会反射被选变量。 *)

Lemma reflected_env_select@{b r s l +} {B : Type@{b}} (Γ Δ Θ : Ctx B)
    (ρ : Ren Δ Γ) (τ : Ren Θ Δ)
  : EnvRenamingN Γ Δ ρ Θ (reflected_env@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Δ Θ τ) ≈S
      reflected_env Γ Θ (ρ ∘Ren τ).
Proof.
  apply env_ext. intros A x.
  transitivity (EnvLookupN Δ A (ρ A x) Θ (reflected_env Δ Θ τ)).
  - apply env_renaming_lookup.
  - transitivity (reflect_ne (TypeReification@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A) Θ
        (ne_var (τ A (ρ A x)))).
    + apply reflected_env_lookup.
    + symmetry. exact (reflected_env_lookup Γ Θ (ρ ∘Ren τ) A x).
Defined.

(** The initial environment keeps each free variable at its own position. *)

(** 初始环境将每个自由变量保留在其原位置。 *)

Definition initial_env@{b r s l +} {B : Type@{b}} (Γ : Ctx B)
  : EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Γ
  := reflected_env Γ Γ idRen.

(** Evaluate in the reflected environment, then reify. The output type
    enforces beta-normal, eta-long shape without a reduction search. *)

(** 在反射环境中求值后再实化；输出类型直接保证 β 正规、η 长的形状，无须
    搜索归约步骤。 *)

Definition nf@{b r s l +} {B : Type@{b}} {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : Nf Γ A
  := reify_sem (TypeReification@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A) Γ
      (EvalN@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t Γ
        (initial_env@{b r s l
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ)).

(** Variables normalize to their type-directed eta expansion. This is a
    theorem about all variable positions and all simple types. *)

(** 变量正规化为其类型导向的 η 展开；此定理覆盖全部变量位置与简单类型。 *)

Lemma nf_var@{b r s l +} {B : Type@{b}} {Γ : Ctx B} {A : Ty B}
    (x : Var Γ A)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} (# x) =
      eta_expand_ne (ne_var x).
Proof.
  unfold nf, initial_env. transitivity
    (reify_sem (TypeReification@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A) Γ
      (reflect_ne (TypeReification@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A) Γ (ne_var x))).
  - apply reify_sem_proper. apply reflected_env_lookup.
  - apply reify_reflect_eta.
Defined.

(** Normalization commutes strictly with syntax renaming. Its proof uses
    semantic equality internally, then reification turns that equality
    into native equality of normal trees. *)

(** 正规化与语法重命名严格交换。证明内部使用语义相等，再由实化将该相等转为
    正规语法树的原生相等。 *)

Lemma nf_rename@{b r s l +} {B : Type@{b}} {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t⟨ρ⟩ =
      (nf@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t)⟨ρ⟩nf.
Proof.
  unfold nf. rewrite <- reify_sem_rename. apply reify_sem_proper.
  etransitivity.
  - exact (eval_rename@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t Δ Δ ρ
      (initial_env Δ)).
  - etransitivity.
    + apply eval_proper. unfold initial_env.
      etransitivity.
      * exact (reflected_env_select@{b r s l
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Δ Δ ρ idRen).
      * symmetry. exact (reflected_env_reindex@{b r s l
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Γ Δ idRen ρ).
    + exact (eval_reindex@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t Γ Δ ρ
        (initial_env Γ)).
Defined.
