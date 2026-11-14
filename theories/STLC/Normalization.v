From Cats Require Export
  STLC.Evaluation
  STLC.NormalDecision.
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
    computed normal trees, without assuming a decision procedure.

    Retraction on every long normal form finally makes embedding and
    normalization a natural isomorphism between the normal and equational
    term presheaves. The optional label decision is kept as a separate
    application at the end. *)

(** * 通过求值正规化

    正规化开放项时，先将自由变量反射到语义环境，再求值该项，最后实化所得
    语义值。三个操作均透明，因此定义了从任意带类型项到 β 正规、η 长语法树
    的可执行映射。

    此处终止性来自元理论中的结构递归，并不是关于每条有向归约序列的断言。
    同样，仅产生形状正确的正规树尚不能证明其与输入 βη 相等。下文由逻辑关系
    基本引理证明此可靠性，由语义相等与实化的保相等性质证明不变性。两者合用
    以计算所得正规树的相等刻画 βη 相等，无须假设判定过程。

    最后，每个长正规形上的回缩使嵌入与正规化构成正规预层与等式项预层之间的
    自然同构。可选的标签判定独立作为末尾的应用。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_tm_scope.

(** ** Normalization and Correctness for a Fixed Signature

    Fix a signature [B] and world equality, semantic and world-law bounds
    to construct reflected initial environments, normalization and its
    correctness laws. The optional decision procedure takes its label
    decision as an explicit argument. Section-local references
    inherit those bindings, so they need no repeated universe instances.
    The semantic bound [s] and world-law bound [l] remain independent. *)

(** ** 固定签名的正规化与正确性

    固定签名 [B] 及世界相等、语义与世界定律界限，构造反射初始环境、正规化与
    正确性定律。可选判定过程将标签判定作为显式参数。节内引用
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

(** Open evaluation commutes with renaming the input and reindexing its
    semantic value. Reflected environments identify the two assignments. *)

(** 开放项求值与输入重命名及语义值重索引交换；反射环境识别两边的赋值。 *)

Lemma eval_initial_rename {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : EvalN t⟨ρ⟩ Δ (initial_env Δ) ≈S
      fmap (SemF A) ρ (EvalN t Γ (initial_env Γ)).
Proof.
  etransitivity.
  - exact (eval_rename t Δ Δ ρ (initial_env Δ)).
  - etransitivity.
    + apply eval_proper. unfold initial_env.
      etransitivity.
      * exact (reflected_env_select Γ Δ Δ ρ idRen).
      * symmetry. exact (reflected_env_reindex Γ Γ Δ idRen ρ).
    + exact (eval_reindex t Γ Δ ρ (initial_env Γ)).
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
  apply eval_initial_rename.
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
  apply eval_reflected_realizes.
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

(** ** Retraction on All Long Normal Forms

    Keep the same signature and semantic bounds. Prove simultaneously
    that evaluating an embedded neutral in a reflected environment agrees
    with reflection, and that reifying an embedded normal form recovers
    its renamed syntax. The function case enters a fresh world; the
    reflected-environment reindexing law identifies its older entries.
    This strengthens idempotence on algorithm outputs to every normal
    tree, without a decision procedure for labels or equality of functions. *)

(** ** 全部长正规形上的回缩

    保持同一签名与语义界限。同时证明：嵌入后的中性项在反射环境中求值，等于
    直接反射；嵌入后的正规形经实化恢复其重命名语法。函数分支进入新鲜世界，
    反射环境的重索引律识别其旧分量。这将算法输出上的幂等性推广到每个正规
    语法树，不需要标签判定过程或函数相等。 *)

Fixpoint eval_embed_ne {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
  : ∀ (Δ : Ctx B) (ρ : Ren Δ Γ),
      EvalN (embed_ne n) Δ (reflected_env Γ Δ ρ) ≈S
        reflect_ne (TypeReification A) Δ (n⟨ρ⟩ne)
with reify_eval_embed_nf {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
  : ∀ (Δ : Ctx B) (ρ : Ren Δ Γ),
      reify_sem (TypeReification A) Δ
        (EvalN (embed_nf v) Δ (reflected_env Γ Δ ρ)) = v⟨ρ⟩nf.
Proof.
  - destruct n as [Γ A x | Γ A U n v | Γ A U n | Γ A U n];
      intros Δ ρ.
    + exact (reflected_env_lookup Γ Δ ρ A x).
    + change ((EvalN (embed_ne n) Δ (reflected_env Γ Δ ρ))
        Δ idRen (EvalN (embed_nf v) Δ (reflected_env Γ Δ ρ)) ≈S
        reflect_ne (TypeReification U) Δ (ne_app (n⟨ρ⟩ne) (v⟨ρ⟩nf))).
      etransitivity.
      * exact (eval_embed_ne Γ (A ⇒ U) n Δ ρ Δ idRen
          (EvalN (embed_nf v) Δ (reflected_env Γ Δ ρ))).
      * cbn [TypeReification reflect_ne reflect_function_value kripke_apply].
        apply reflect_ne_proper.
        rewrite rename_ne_id, (reify_eval_embed_nf Γ A v Δ ρ).
        reflexivity.
    + change (fst (EvalN (embed_ne n) Δ (reflected_env Γ Δ ρ)) ≈S
        reflect_ne (TypeReification A) Δ (ne_fst (n⟨ρ⟩ne))).
      pose proof (eval_embed_ne Γ (A × U) n Δ ρ) as h.
      destruct (EvalN (embed_ne n) Δ (reflected_env Γ Δ ρ)) as [a u].
      exact (fst h).
    + change (snd (EvalN (embed_ne n) Δ (reflected_env Γ Δ ρ)) ≈S
        reflect_ne (TypeReification U) Δ (ne_snd (n⟨ρ⟩ne))).
      pose proof (eval_embed_ne Γ (A × U) n Δ ρ) as h.
      destruct (EvalN (embed_ne n) Δ (reflected_env Γ Δ ρ)) as [a u].
      exact (snd h).
  - destruct v as [Γ p n | Γ | Γ A U v w | Γ A U v]; intros Δ ρ.
    + change (nf_base (lower (EvalN (embed_ne n) Δ
        (reflected_env Γ Δ ρ))) = nf_base (n⟨ρ⟩ne)).
      f_equal. exact (lower (eval_embed_ne Γ (ty_base p) n Δ ρ)).
    + reflexivity.
    + cbn [embed_nf EvalN TypeReification reify_sem rename_nf].
      f_equal.
      * exact (reify_eval_embed_nf Γ A v Δ ρ).
      * exact (reify_eval_embed_nf Γ U w Δ ρ).
    + change (nf_lam (reify_sem (TypeReification U) (Δ ▻ A)
        (EvalN (embed_nf v) (Δ ▻ A)
          (fmap (EnvF Γ) wkRen (reflected_env Γ Δ ρ),
            reflect_ne (TypeReification A) (Δ ▻ A) (ne_var var_zero)))) =
        nf_lam (v⟨ρ^↑Ren⟩nf)).
      f_equal. transitivity (reify_sem (TypeReification U) (Δ ▻ A)
        (EvalN (embed_nf v) (Δ ▻ A)
          (reflected_env (Γ ▻ A) (Δ ▻ A) (ρ^↑Ren)))).
      * apply reify_sem_proper. apply eval_proper. split.
        -- exact (reflected_env_reindex Γ Δ (Δ ▻ A) ρ wkRen).
        -- reflexivity.
      * exact (reify_eval_embed_nf (Γ ▻ A) U v (Δ ▻ A) (ρ^↑Ren)).
Defined.

(** Normalization is a strict retraction of the embedding on every long
    normal tree, not just those previously produced by normalization. *)

(** 正规化在每个长正规语法树上都是嵌入的严格回缩，不限于此前已经正规化
    得到的语法树。 *)

Lemma nf_embed_nf {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
  : nf (embed_nf v) = v.
Proof.
  unfold nf, initial_env. rewrite reify_eval_embed_nf. apply rename_nf_id.
Defined.

(** A supplied long normal form represents a term exactly when it is
    that term's computed normal form. This characterizes every normal
    tree, without a label decision or a selected reduction strategy. *)

(** 给定长正规形表示某项，当且仅当它就是该项计算所得的正规形。此性质刻画
    每个正规语法树，不需要标签判定或选定归约策略。 *)

Definition normal_form_characterization@{e +}
    {Γ : Ctx B} {A : Ty B} (t : Tm Γ A) (v : Nf Γ A)
  : TmEq@{b e _} t (embed_nf v) ↔ nf t = v.
Proof.
  split.
  - intros h. rewrite <- (nf_embed_nf v). exact (nf_tm_eq h).
  - intros h. rewrite <- h. apply nf_sound.
Defined.

(** Normalization is natural from equational syntax to structural normal
    syntax. The equation-evidence bound [q] is independent of semantics. *)

(** 正规化是从等式语法到结构正规语法的自然变换；等式证据界 [q] 独立于语义。 *)

Program Definition NormalizeN@{q +} (A : Ty B)
  : (TmRenamingPsh A : Functor
      ((RenamingCat B : Cat@{b b r l l})^op) SetCat@{b q _ _ _ _ _})
      ⇒ NfPsh A
  :=
  {|nt Γ :=
     {|func := nf
     |}
  |}.
Next Obligation. intros t u h. exact (nf_tm_eq h). Defined.
Next Obligation. intros t. apply nf_rename. Defined.

(** The normal embedding followed by normalization is the identity on
    all normal forms, as a natural-transformation equation. *)

(** 正规嵌入后接正规化，是全部正规形上的恒等自然变换。 *)

Definition normalize_embed_triangle (A : Ty B)
  : (NormalizeN A ∘Nv NfEmbedN A) ≈N idN.
Proof. intros Γ v. apply nf_embed_nf. Defined.

(** The opposite composite is the identity in beta/eta equality. *)

(** 反向复合在 βη 相等下是恒等变换。 *)

Definition embed_normalize_triangle (A : Ty B)
  : (NfEmbedN A ∘Nv NormalizeN A) ≈N idN.
Proof. intros Γ t. symmetry. apply nf_sound. Defined.

(** The normal and equational term presheaves are naturally isomorphic.
    Components retain the normalization algorithm as their inverse; this
    does not identify functor records or equation witnesses. *)

(** 正规预层与等式项预层自然同构，各分量保留正规化算法作为逆映射；不识别
    函子记录或等式见证。 *)

Definition NormalFormsIsoN (A : Ty B)
  : NfPsh A ≅N TmRenamingPsh A.
Proof.
  exists (NfEmbedN A). intros Γ. exists (NormalizeN A Γ). split.
  - intros v. apply nf_embed_nf.
  - intros t. symmetry. apply nf_sound.
Defined.

(** ** Optional Equality Decision

    An explicit equality decision for base labels enables comparison of
    computed normal trees. All preceding normalization and natural
    isomorphism theorems remain independent of this additional input. *)

(** ** 可选的相等判定

    显式的基标签相等判定允许比较计算所得的正规语法树。此前的正规化与自然
    同构定理均独立于这个额外输入。 *)

(** Decide beta/eta equality using the explicit base-label decision.
    Equal computed trees yield an equational derivation in the chosen
    evidence universe; unequal trees refute every such derivation by
    invariance. The decision keeps either witness as Type-valued data.
    All preceding normalization theorems remain unconditional. *)

(** 使用显式基标签判定来判定 βη 相等。计算所得树相同时，在选定证据宇宙中
    产生等式推导；不同时，由不变性反驳任意这样的推导。判定将任一分支的见证
    保留为 Type 值数据。此前的全部正规化定理仍然无条件成立。 *)

Definition tm_eq_decision@{e +}
    (d : ∀ p q : B, Decision (p = q))
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Decision (TmEq@{b e _} t u)
  := decision_iff (tm_eq_nf t u) (nf_eq_decision d (nf t) (nf u)).

End Normalization.
