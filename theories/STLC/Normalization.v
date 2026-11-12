From Cats Require Export STLC.Evaluation.
From Cats Require Import
  STLC.EvaluationEquivalence
  STLC.LogicalRelation
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
    its input. Below, the logical-relation fundamental lemma proves this
    soundness theorem; semantic equality and respectful reification prove
    invariance. Together they characterize beta/eta equality by equality of
    computed normal trees, without assuming a decision procedure. *)

(** * 通过求值正规化

    正规化开放项时，先将自由变量反射到语义环境，再求值该项，最后实化所得
    语义值。三个操作均透明，因此定义了从任意带类型项到 β 正规、η 长语法树
    的可执行映射。

    此处终止性来自元理论中的结构递归，并不是关于每条有向归约序列的断言。
    同样，仅产生形状正确的正规树尚不能证明其与输入 βη 相等。下文由逻辑关系
    基本引理证明此可靠性，由语义相等与实化的保相等性质证明不变性。两者合用
    以计算所得正规树的相等刻画 βη 相等，无须假设判定过程。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_tm_scope.

(** Fix the signature, world equality, semantic and world-law bounds
    once for this construction and its laws. Section-local references
    inherit those bindings, so they need no repeated universe instances.
    The semantic bound [s] and world-law bound [l] remain independent. *)

(** 为本构造及其定律一次固定签名、世界相等、语义与世界定律界限。节内引用
    继承这些绑定，无须反复写宇宙实例；语义界限 [s] 与世界定律界限 [l] 仍
    相互独立。 *)

Section Normalization.
Universes b r s l.
Context {B : Type@{b}}.

(** Reflect a renamed collection of free variables. Recursion follows
    the source context; the target world remains fixed. This more general
    environment makes the context coherence of initialization explicit. *)

(** 反射经重命名的一组自由变量。递归沿源上下文进行，目标世界保持不变。
    此更一般的环境使初始化的上下文相容性能够显式陈述。 *)

Fixpoint reflected_env (Γ : Ctx B)
  : ∀ Δ : Ctx B, Ren Δ Γ →
      (EnvF Γ : Functor ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) Δ.
Proof.
  destruct Γ as [| Γ A]; intros Δ ρ.
  - exact tt.
  - exact (reflected_env Γ Δ (λ U x, ρ U (var_succ x)),
      reflect_ne (TypeReification A) Δ
        (ne_var (ρ A var_zero))).
Defined.

(** Lookup recovers precisely the reflected variable at its renamed
    position. This law needs neither equality of labels nor proof fields. *)

(** 查找恰好恢复重命名位置处的反射变量，不比较标签或证明字段的相等。 *)

Lemma reflected_env_lookup (Γ : Ctx B)
  : ∀ (Δ : Ctx B) (ρ : Ren Δ Γ) (A : Ty B) (x : Var Γ A),
      EnvLookupN Γ A x Δ (reflected_env Γ Δ ρ) ≈S
        reflect_ne (TypeReification A) Δ
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

Global Instance reflected_env_proper (Γ Δ : Ctx B)
  : Proper (RenEq ==> [≈S]) (reflected_env Γ Δ).
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

Lemma reflected_env_reindex (Γ : Ctx B)
  : ∀ (Δ Θ : Ctx B) (ρ : Ren Δ Γ) (τ : Ren Θ Δ),
      fmap (EnvF Γ) τ (reflected_env Γ Δ ρ) ≈S
        reflected_env Γ Θ (ρ ∘Ren τ).
Proof.
  induction Γ as [| Γ IH A]; intros Δ Θ ρ τ.
  - exact tt.
  - split.
    + exact (IH Δ Θ (λ U x, ρ U (var_succ x)) τ).
    + exact (reflect_ne_rename (TypeReification A) Δ Θ τ
        (ne_var (ρ A var_zero))).
Defined.

(** Selecting reflected entries composes their renamings. In particular,
    selecting an initial environment reflects the selected variables. *)

(** 选取反射后的分量会复合其重命名。特别地，选取初始环境会反射被选变量。 *)

Lemma reflected_env_select (Γ Δ Θ : Ctx B)
    (ρ : Ren Δ Γ) (τ : Ren Θ Δ)
  : EnvRenamingN Γ Δ ρ Θ (reflected_env Δ Θ τ) ≈S
      reflected_env Γ Θ (ρ ∘Ren τ).
Proof.
  apply env_ext. intros A x.
  transitivity (EnvLookupN Δ A (ρ A x) Θ (reflected_env Δ Θ τ)).
  - apply env_renaming_lookup.
  - transitivity (reflect_ne (TypeReification A) Θ
        (ne_var (τ A (ρ A x)))).
    + apply reflected_env_lookup.
    + symmetry. exact (reflected_env_lookup Γ Θ (ρ ∘Ren τ) A x).
Defined.

(** The initial environment keeps each free variable at its own position. *)

(** 初始环境将每个自由变量保留在其原位置。 *)

Definition initial_env (Γ : Ctx B)
  : EnvF Γ Γ
  := reflected_env Γ Γ idRen.

(** Evaluate in the reflected environment, then reify. The output type
    enforces beta-normal, eta-long shape without a reduction search. *)

(** 在反射环境中求值后再实化；输出类型直接保证 β 正规、η 长的形状，无须
    搜索归约步骤。 *)

Definition nf {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : Nf Γ A
  := reify_sem (TypeReification A) Γ (EvalN t Γ (initial_env Γ)).

(** Variables normalize to their type-directed eta expansion. This is a
    theorem about all variable positions and all simple types. *)

(** 变量正规化为其类型导向的 η 展开；此定理覆盖全部变量位置与简单类型。 *)

Lemma nf_var {Γ : Ctx B} {A : Ty B}
    (x : Var Γ A)
  : nf (# x) = eta_expand_ne (ne_var x).
Proof.
  unfold nf, initial_env. transitivity
    (reify_sem (TypeReification A) Γ
      (reflect_ne (TypeReification A) Γ (ne_var x))).
  - apply reify_sem_proper. apply reflected_env_lookup.
  - apply reify_reflect_eta.
Defined.

(** Normalization commutes strictly with syntax renaming. Its proof uses
    semantic equality internally, then reification turns that equality
    into native equality of normal trees. *)

(** 正规化与语法重命名严格交换。证明内部使用语义相等，再由实化将该相等转为
    正规语法树的原生相等。 *)

Lemma nf_rename {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : nf t⟨ρ⟩ = (nf t)⟨ρ⟩nf.
Proof.
  unfold nf. rewrite <- reify_sem_rename. apply reify_sem_proper.
  etransitivity.
  - exact (eval_rename t Δ Δ ρ (initial_env Δ)).
  - etransitivity.
    + apply eval_proper. unfold initial_env.
      etransitivity.
      * exact (reflected_env_select Γ Δ Δ ρ idRen).
      * symmetry. exact (reflected_env_reindex Γ Γ Δ idRen ρ).
    + exact (eval_reindex t Γ Δ ρ (initial_env Γ)).
Defined.

(** Beta/eta equal inputs produce literally the same normal syntax tree.
    Semantic extensional equality suffices because reification is a
    respectful map into the native-equality setoid of normal forms. *)

(** βη 相等的输入产生完全相同的正规语法树。语义外延相等已经足够，因为
    实化是到以原生相等比较的正规形广集的保相等映射。 *)

Lemma nf_tm_eq@{e +} {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : TmEq@{b e _} t u)
  : nf t = nf u.
Proof.
  unfold nf. apply reify_sem_proper.
  exact (eval_tm_eq h Γ (initial_env Γ)).
Defined.

(** Full normalization soundness for arbitrary open terms. The fundamental
    lemma uses the identity syntactic assignment and the reflected initial
    environment. Reification yields the equational witness, whose bound
    remains independent of the semantic value bound. *)

(** 任意开放项的完整正规化可靠性。基本引理使用恒等语法赋值与反射初始环境；
    实化给出等式见证，其界限仍独立于语义值界限。 *)

Definition nf_sound@{e +} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : TmEq@{b e _} t (embed_nf (nf t)).
Proof.
  refine (realizes_reify A Γ t (EvalN t Γ (initial_env Γ)) _).
  refine (realizes_tm_eq A Γ t[idSub] t _
    (tm_eq_of_eq (subst_id t)) _).
  apply eval_realizes. apply env_realizes_reflected.
  intros U x. exact (reflected_env_lookup Γ Γ idRen U x).
Defined.

(** Equality of computed trees produces a beta/eta derivation by following
    soundness from each input to its normal form. Native tree equality
    transports the middle term; no equality of derivation witnesses is used. *)

(** 计算所得树的相等产生 βη 推导：可靠性将两边输入接到各自的正规形，原生
    树相等输运中间项；不使用推导见证之间的相等。 *)

Definition nf_eq_tm_eq@{e +} {Γ : Ctx B} {A : Ty B}
    (t u : Tm Γ A) (h : nf t = nf u)
  : TmEq@{b e _} t u.
Proof.
  refine (tm_eq_trans (nf_sound t) _).
  rewrite h. exact (tm_eq_sym (nf_sound u)).
Defined.

(** Beta/eta equality is characterized by equality of computed normal
    trees. The Type-valued equivalence retains both maps and constructs
    equational witnesses in the independently chosen evidence universe.
    Deciding tree equality is a separate question. *)

(** βη 相等由计算所得正规树的相等刻画。Type 值逻辑等价保留双向映射，并在
    独立选定的证据宇宙中构造等式见证。判定树相等是另一问题。 *)

Definition tm_eq_nf@{e +} {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : TmEq@{b e _} t u ↔ nf t = nf u
  := (nf_tm_eq, nf_eq_tm_eq t u).

(** Normalizing the embedded output again leaves that output unchanged.
    This is strict equality of syntax trees, derived from soundness and
    invariance rather than a claim about all reduction paths. *)

(** 将输出嵌入后再次正规化，仍得到原输出。这是由可靠性与不变性导出的语法树
    严格相等，而非关于全部归约路径的断言。 *)

Lemma nf_idempotent {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : nf (embed_nf (nf t)) = nf t.
Proof. symmetry. exact (nf_tm_eq (nf_sound t)). Defined.

End Normalization.
