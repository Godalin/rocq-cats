From Cats Require Export STLC.Reification.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.FiniteProducts
  Cat.Natural
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Terminal
  Instance.Set.Kripke.

(** * Evaluation in Semantic Environments

    A syntactic context is interpreted by a presheaf of environments. At
    a world [Δ], an environment for [Γ] supplies a semantic value in [Δ]
    for each declaration of [Γ]. Extending [Γ] is a pointwise product;
    changing [Δ] reindexes every stored value together.

    Evaluation is a natural transformation, constructed by recursion on
    the input term. Thus equality preservation and world coherence are
    part of evaluation itself. Abstraction reuses coherent Kripke currying,
    rather than storing an unconstrained family of future evaluations. *)

(** * 语义环境中的求值

    语法上下文解释为环境预层。在世界 [Δ] 中，[Γ] 的环境为 [Γ] 的每个声明
    提供一个位于 [Δ] 的语义值。扩张 [Γ] 使用逐点积；更换 [Δ] 则同时重索引
    全部保存的值。

    求值沿输入项递归构造为自然变换，因此保相等性质与世界相容性本就是求值的
    一部分。抽象复用相容的 Kripke 柯里化，不保存缺乏约束的未来求值族。 *)

Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasTerminal.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** ** Environments and Evaluation for a Fixed Signature

    Fix a signature [B] and world equality, semantic and world-law bounds
    to construct environment presheaves and natural evaluation maps.
    Section-local references
    inherit those bindings, so they need no repeated universe instances.
    The semantic bound [s] and world-law bound [l] remain independent. *)

(** ** 固定签名的环境与求值

    固定签名 [B] 及世界相等、语义与世界定律界限，构造环境预层与自然求值
    映射。节内引用
    继承这些绑定，无须反复写宇宙实例；语义界限 [s] 与世界定律界限 [l] 仍
    相互独立。 *)

Section Evaluation.
Universes b r s l.
Context {B : Type@{b}}.

(** Empty environments are singleton values; context extension stores the
    older environment and one new value. The semantic bound is the same
    explicit internal bound as in [SemF], independent of world-law size. *)

(** 空环境是单元素值；上下文扩张保存旧环境与一个新值。语义界限沿用 [SemF]
    中显式的内部界限，与世界定律的大小独立。 *)

Fixpoint EnvF (Γ : Ctx B)
  : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}
  := match Γ with
  | ctx_empty => ConstF ((RenamingCat B)^op) (C := SetCat) UnitS
  | ctx_snoc Γ A => PointwiseProductF (EnvF Γ) (SemF A)
  end.

(** Typed lookup is a natural transformation. Older positions project
    the environment prefix; the newest marker projects the new value.
    No equality test on type labels or binding types is needed. *)

(** 带类型查找是自然变换。旧位置投影出环境前缀，最新标记投影出新值；无须
    判定类型标签或绑定类型的相等。 *)

Fixpoint EnvLookupN (Γ : Ctx B)
  : ∀ A : Ty B, Var Γ A → EnvF Γ ⇒ SemF A.
Proof.
  destruct Γ as [| Γ U]; intros A x.
  - destruct x.
  - destruct x as [x | x].
    + exact (EnvLookupN Γ A x ∘Nv
        PointwiseFstN _ _ (EnvF Γ) (SemF U)).
    + destruct x. exact (PointwiseSndN _ _ (EnvF Γ) (SemF U)).
Defined.

(** Environments are determined by their typed observations. The resulting
    equality is the environment's componentwise setoid relation, not
    native equality of semantic functions or stored law witnesses. *)

(** 环境由其带类型观察确定。所得相等是环境逐分量的广集关系，不是语义函数
    或保存定律见证的原生相等。 *)

Lemma env_ext (Γ : Ctx B)
  : ∀ (Δ : Ctx B) (γ δ : EnvF Γ Δ),
      (∀ (A : Ty B) (x : Var Γ A),
        EnvLookupN Γ A x Δ γ ≈S EnvLookupN Γ A x Δ δ) → γ ≈S δ.
Proof.
  induction Γ as [| Γ IH U]; intros Δ γ δ h.
  - exact tt.
  - destruct γ as [γ a], δ as [δ b]. split.
    + apply IH. intros A x. exact (h A (var_succ x)).
    + exact (h U var_zero).
Defined.

(** A syntactic renaming selects an environment's entries. This action
    changes the context being interpreted while keeping the world fixed;
    it differs from reindexing semantic values along a world arrow. *)

(** 语法重命名选取环境分量。此作用更换被解释的上下文而保持世界不变，区别
    于沿世界箭头对语义值重索引。 *)

Fixpoint EnvRenamingN (Γ : Ctx B)
  : ∀ Δ : Ctx B, Ren Δ Γ → EnvF Δ ⇒ EnvF Γ.
Proof.
  destruct Γ as [| Γ A]; intros Δ ρ.
  - exact (PointwiseTerminalN _ _ (EnvF Δ)).
  - exact (PointwisePairN _ _
      (EnvRenamingN Γ Δ (λ U x, ρ U (var_succ x)))
      (EnvLookupN Δ A (ρ A var_zero))).
Defined.

(** Looking up a selected environment is looking up the renamed variable
    in the original environment. *)

(** 在选取后的环境中查找，等于在原环境中查找重命名后的变量。 *)

Lemma env_renaming_lookup (Γ : Ctx B)
  : ∀ (Δ Θ : Ctx B) (ρ : Ren Δ Γ) (γ : EnvF Δ Θ)
      (A : Ty B) (x : Var Γ A),
      EnvLookupN Γ A x Θ (EnvRenamingN Γ Δ ρ Θ γ) ≈S
        EnvLookupN Δ A (ρ A x) Θ γ.
Proof.
  induction Γ as [| Γ IH U]; intros Δ Θ ρ γ A x.
  - destruct x.
  - destruct x as [x | x].
    + exact (IH Δ Θ (λ T y, ρ T (var_succ y)) γ A x).
    + destruct x. reflexivity.
Defined.

(** Environment selection respects pointwise equality of renamings. *)

(** 环境选取保持重命名的逐点相等。 *)

Global Instance EnvRenamingN_proper (Γ Δ : Ctx B)
  : Proper (RenEq ==> NatEq) (EnvRenamingN Γ Δ).
Proof.
  intros ρ τ h Θ γ. apply env_ext. intros A x.
  etransitivity; [apply env_renaming_lookup |].
  rewrite (h A x). symmetry. apply env_renaming_lookup.
Defined.

(** Selecting by the identity preserves every environment. *)

(** 按恒等选取保留每个环境。 *)

Lemma env_renaming_id (Γ : Ctx B)
  : EnvRenamingN Γ Γ idRen ≈N idN.
Proof.
  intros Θ γ. apply env_ext. intros A x.
  exact (env_renaming_lookup Γ Γ Θ idRen γ A x).
Defined.

(** Selecting along a composite is successive selection in the reverse
    order of syntactic context maps. The comparison is natural equality. *)

(** 沿复合选取等于按语法上下文映射的反向顺序逐次选取，比较使用自然相等。 *)

Lemma env_renaming_comp {Γ Δ Θ : Ctx B}
    (ρ : Ren Δ Γ) (τ : Ren Θ Δ)
  : EnvRenamingN Γ Θ (ρ ∘Ren τ) ≈N
      (EnvRenamingN Γ Δ ρ ∘Nv EnvRenamingN Δ Θ τ).
Proof.
  intros Ξ γ. apply env_ext. intros A x. symmetry.
  transitivity (EnvLookupN Δ A (ρ A x) Ξ (EnvRenamingN Δ Θ τ Ξ γ)).
  - apply env_renaming_lookup.
  - transitivity (EnvLookupN Θ A (τ A (ρ A x)) Ξ γ).
    + apply env_renaming_lookup.
    + symmetry. exact (env_renaming_lookup Γ Θ Ξ (ρ ∘Ren τ) γ A x).
Defined.

(** Lifting a renaming under a binder preserves the new environment
    entry and selects only the older entries. *)

(** 在绑定下提升重命名时，保留新环境分量，只选取旧分量。 *)

Lemma env_renaming_lift {Γ Δ : Ctx B} {A : Ty B}
    (ρ : Ren Δ Γ) (Θ : Ctx B) (γ : EnvF Δ Θ) (a : SemF A Θ)
  : EnvRenamingN (Γ ▻ A) (Δ ▻ A) (ρ^↑Ren) Θ (γ, a) ≈S
      (EnvRenamingN Γ Δ ρ Θ γ, a).
Proof.
  apply env_ext. intros U [x | x].
  - etransitivity; [apply env_renaming_lookup |].
    symmetry. exact (env_renaming_lookup Γ Δ Θ ρ γ U x).
  - destruct x. reflexivity.
Defined.

(** Weakening drops the newest environment entry. In particular, a
    weakened term is evaluated independently of the new argument. *)

(** 弱化丢弃环境的最新分量。特别地，弱化项的求值与新实参无关。 *)

Lemma env_renaming_weaken {Γ : Ctx B} {A : Ty B}
    (Θ : Ctx B) (γ : EnvF Γ Θ) (a : SemF A Θ)
  : EnvRenamingN Γ (Γ ▻ A) wkRen Θ (γ, a) ≈S γ.
Proof.
  apply env_ext. intros U x.
  exact (env_renaming_lookup Γ (Γ ▻ A) Θ wkRen (γ, a) U x).
Defined.

(** Within the common semantic bound, currying needs no outer lift of
    the parameter. Its components and laws are the existing general
    Kripke construction, specialized to this semantic family. *)

(** 在共同语义界限内部，柯里化无须额外提升参数。其分量与定律直接使用既有
    的一般 Kripke 构造，专化到此语义族。 *)

Program Definition SemanticCurryN
    (A U : Ty B)
    (H : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _})
    (α : PointwiseProductF H (SemF A) ⇒ SemF U)
  : H ⇒ SemF (A ⇒ U)
  :=
  {|nt Δ :=
     {|func h := kripke_curry_at (SemF A) (SemF U) H α Δ h
     |}
  |}.
Next Obligation.
  intros h. symmetry. apply kripke_curry_at_reindex.
Defined.

(** Applying a semantic function to an argument in its current world is
    natural. The generic reindexing theorem supplies exactly this law. *)

(** 在当前世界将语义函数应用于实参是自然的；一般重索引定理恰好提供此定律。 *)

Program Definition SemanticApplyN (A U : Ty B)
  : PointwiseProductF (SemF (A ⇒ U)) (SemF A) ⇒ SemF U
  :=
  {|nt Δ :=
     {|func p := kripke_eval (SemF A) (SemF U) (fst p) (snd p)
     |}
  |}.
Next Obligation.
  intros [f x] [g y] [h k]. apply kripke_eval_proper; assumption.
Defined.
Next Obligation.
  intros [k x]. symmetry.
  exact (kripke_eval_reindex (SemF A) (SemF U) f k x).
Defined.

(** Every raw typed term acts on environments. Pairing, projections and
    unit use pointwise finite products; lambda and application use the
    preceding wrappers around generic coherent Kripke operations.

    A lambda evaluated at world [Δ] with environment [γ] must accept any
    future arrow [ρ : Ren Θ Δ] and argument [a] at [Θ]. It evaluates its
    body with [(fmap (EnvF Γ) ρ γ, a)]: first transport all older values,
    then append the argument. Application uses the identity future arrow.
    Reification can instead use weakening to enter a fresh binder. These
    are two observations of the same coherent function value. *)

(** 每个带类型原始项都作用于环境。配对、投影与单位使用逐点有限积；λ 与应用
    使用前述一般相容 Kripke 操作的包装。

    在世界 [Δ] 与环境 [γ] 中求值后的 λ，须接受任意未来箭头
    [ρ : Ren Θ Δ] 与位于 [Θ] 的实参 [a]。它使用环境
    [(fmap (EnvF Γ) ρ γ, a)] 求值项体：先运输全部旧值，再追加实参。
    应用使用恒等未来箭头；实化则可使用弱化进入新绑定。这是对同一个相容
    函数值的两种观察。 *)

Fixpoint EvalN {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : EnvF Γ ⇒ SemF A.
Proof.
  destruct t as [Γ A x | Γ | Γ A U t u | Γ A U t | Γ A U t |
    Γ A U t | Γ A U f a].
  - exact (EnvLookupN Γ A x).
  - exact (PointwiseTerminalN _ _ (EnvF Γ)).
  - exact (PointwisePairN _ _ (EvalN _ _ t) (EvalN _ _ u)).
  - exact (PointwiseFstN _ _ (SemF A) (SemF U) ∘Nv EvalN _ _ t).
  - exact (PointwiseSndN _ _ (SemF A) (SemF U) ∘Nv EvalN _ _ t).
  - exact (SemanticCurryN A U (EnvF Γ) (EvalN _ _ t)).
  - exact (SemanticApplyN A U ∘Nv
      PointwisePairN _ _ (EvalN _ _ f) (EvalN _ _ a)).
Defined.

(** Evaluation as a component operation. The environment may live in a
    different world from the term's syntactic context. *)

(** 作为分量操作的求值。环境所在的世界可以不同于项的语法上下文。 *)

Definition eval {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A) (Δ : Ctx B)
    (γ : EnvF Γ Δ)
  : SemF A Δ
  := EvalN t Δ γ.

(** Equivalent environments yield equivalent values, including at
    function types where equality observes all future applications. *)

(** 等价环境产生等价值；函数类型处的相等观察全部未来应用。 *)

Global Instance eval_proper {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A) (Δ : Ctx B)
  : Proper ([≈S] ==> [≈S]) (eval t Δ).
Proof. exact (@func_proper _ _ (EvalN t Δ)). Defined.

(** Evaluation commutes with reindexing all entries of its environment. *)

(** 求值与同时重索引环境的全部分量交换。 *)

Lemma eval_reindex {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A) (Δ Θ : Ctx B) (ρ : Ren Θ Δ)
    (γ : EnvF Γ Δ)
  : eval t Θ (fmap (EnvF Γ) ρ γ) ≈S fmap (SemF A) ρ (eval t Δ γ).
Proof. exact (nt_naturality (EvalN t) ρ γ). Defined.

(** A semantic beta equation: applying an evaluated abstraction agrees
    with evaluating its body in the environment extended by the argument.
    The only comparison is the environment functor's identity law. This
    does not yet assert compatibility with syntactic substitution. *)

(** 语义 β 方程：应用求值后的抽象，等于在按实参扩张的环境中求值其项体。
    唯一所需比较是环境函子的单位律；此处尚未断言与语法替换的相容性。 *)

Lemma eval_lam_β {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) (Δ : Ctx B) (γ : EnvF Γ Δ) (a : SemF A Δ)
  : kripke_eval (SemF A) (SemF U) (eval (ƛ t) Δ γ) a ≈S
      eval t Δ (γ, a).
Proof.
  cbn [eval EvalN SemanticCurryN nt kripke_eval kripke_curry_at
    kripke_apply].
  apply func_proper. split.
  - exact (functor_id _ _ (EnvF Γ) γ).
  - reflexivity.
Defined.

(** Syntactic renaming is evaluated by selecting environment entries.
    The abstraction case uses both binder lifting and naturality of that
    selection, so it applies in every future world. *)

(** 语法重命名通过选取环境分量来求值。抽象情形同时使用绑定提升与选取的
    自然性，因此适用于每个未来世界。 *)

Lemma eval_rename {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : ∀ (Δ Θ : Ctx B) (ρ : Ren Δ Γ)
      (γ : EnvF Δ Θ),
      eval t⟨ρ⟩ Θ γ ≈S eval t Θ (EnvRenamingN Γ Δ ρ Θ γ).
Proof.
  induction t as [Γ A x | Γ | Γ A U t IHt u IHu |
    Γ A U t IH | Γ A U t IH | Γ A U t IH |
    Γ A U f IHf a IHa]; intros Δ Θ ρ γ.
  - symmetry. exact (env_renaming_lookup Γ Δ Θ ρ γ A x).
  - exact tt.
  - split; [apply IHt | apply IHu].
  - exact (@func_proper _ _
      (PointwiseFstN _ _ (SemF A) (SemF U) Θ) _ _ (IH Δ Θ ρ γ)).
  - exact (@func_proper _ _
      (PointwiseSndN _ _ (SemF A) (SemF U) Θ) _ _ (IH Δ Θ ρ γ)).
  - intros Ξ τ a.
    change (eval t⟨ρ^↑Ren⟩ Ξ (fmap (EnvF Δ) τ γ, a) ≈S
      eval t Ξ (fmap (EnvF Γ) τ (EnvRenamingN Γ Δ ρ Θ γ), a)).
    etransitivity; [apply IH |]. apply eval_proper.
    etransitivity; [apply env_renaming_lift |]. split.
    + exact (nt_naturality (EnvRenamingN Γ Δ ρ) τ γ).
    + reflexivity.
  - apply kripke_eval_proper; [apply IHf | apply IHa].
Defined.

End Evaluation.
