From Cats Require Export STLC.Evaluation.
From Cats Require Import
  STLC.Substitution
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.FiniteProducts
  Cat.Natural
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Terminal
  Instance.Set.Kripke.

(** * Substitution in Semantic Environments

    A simultaneous substitution supplies syntax for every variable. By
    evaluating these assigned terms in one environment, we obtain an
    environment for the substituted context. This assignment is a natural
    transformation: all its entries commute with changing the world.

    The substitution lemma compares evaluating [t[σ]] with evaluating [t]
    in this new environment. Its binder case combines syntactic weakening,
    preservation of the fresh variable, and naturality. All comparisons
    use the semantic setoid relations, including at function types. *)

(** * 语义环境中的替换

    同时替换为每个变量提供语法项。在同一个环境中求值这些所赋的项，就得到
    被替换上下文的环境。这个赋值是自然变换：每个分量都与更换世界交换。

    替换引理比较 [t[σ]] 的求值与 [t] 在这个新环境中的求值。绑定情形结合
    语法弱化、新变量的保持与自然性。全部比较使用语义广集关系，包括函数
    类型处的比较。 *)

Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasTerminal.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_tm_scope.

(** ** Natural Substitution Maps

    Fix a signature [B] and the world equality, semantic and world-law
    bounds. Using the chosen setoid products and terminal object enabled
    above, evaluate substitutions as environment maps and prove lookup,
    binder, composition and term-substitution compatibility. *)

(** ** 自然替换映射

    固定签名 [B] 及世界相等、语义与世界定律界限。使用上文启用的选定广集积
    与终对象，将替换求值为环境映射，并证明查找、绑定、复合及项替换相容性。 *)

Section EvaluationSubstitution.
Universes b r s l.
Context {B : Type@{b}}.

(** Evaluate every assignment of a substitution in the input environment.
    The functor boundary fixes the same independent bounds as evaluation;
    recursive calls and subsequent laws inherit them implicitly. *)

(** 在输入环境中求值替换的每个赋值。函子边界固定与求值相同的独立界限；
    递归调用与后续定律隐式继承这些界限。 *)

Fixpoint EvalSubN (Γ : Ctx B)
  : ∀ Δ : Ctx B, Sub Δ Γ →
      (EnvF Δ : Functor ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) ⇒ EnvF Γ.
Proof.
  destruct Γ as [| Γ A]; intros Δ σ.
  - exact (PointwiseTerminalN _ _ (EnvF Δ)).
  - exact (PointwisePairN _ _
      (EvalSubN Γ Δ (λ U x, σ U (var_succ x)))
      (EvalN (σ A var_zero))).
Defined.

(** Looking up an evaluated substitution yields the evaluated assignment. *)

(** 查找求值后的替换，得到对应赋值的求值。 *)

Lemma eval_sub_lookup (Γ : Ctx B)
  : ∀ (Δ Θ : Ctx B) (σ : Sub Δ Γ) (γ : EnvF Δ Θ)
      (A : Ty B) (x : Var Γ A),
      EnvLookupN Γ A x Θ (EvalSubN Γ Δ σ Θ γ) ≈S
        eval (σ A x) Θ γ.
Proof.
  induction Γ as [| Γ IH U]; intros Δ Θ σ γ A x.
  - destruct x.
  - destruct x as [x | x].
    + exact (IH Δ Θ (λ T y, σ T (var_succ y)) γ A x).
    + destruct x. reflexivity.
Defined.

(** Pointwise structural equality of assignments gives natural equality
    of the resulting environment maps. *)

(** 赋值的逐点结构相等给出所得环境映射的自然相等。 *)

Global Instance EvalSubN_proper (Γ Δ : Ctx B)
  : Proper (SubEq ==> NatEq) (EvalSubN Γ Δ).
Proof.
  intros σ τ h Θ γ. apply env_ext. intros A x.
  etransitivity; [apply eval_sub_lookup |].
  rewrite (h A x). symmetry. apply eval_sub_lookup.
Defined.

(** Variable-only substitution recovers the existing selection map. *)

(** 仅由变量组成的替换恢复已有的环境选取映射。 *)

Lemma eval_sub_renaming {Γ Δ : Ctx B} (ρ : Ren Δ Γ)
  : EvalSubN Γ Δ (RenSub ρ) ≈N EnvRenamingN Γ Δ ρ.
Proof.
  intros Θ γ. apply env_ext. intros A x.
  etransitivity; [apply eval_sub_lookup |].
  symmetry. apply env_renaming_lookup.
Defined.

(** The identity substitution leaves the semantic environment unchanged. *)

(** 恒等替换保持语义环境不变。 *)

Lemma eval_sub_id (Γ : Ctx B)
  : EvalSubN Γ Γ idSub ≈N idN.
Proof.
  intros Θ γ. apply env_ext. intros A x.
  exact (eval_sub_lookup Γ Γ Θ idSub γ A x).
Defined.

(** Binder lifting evaluates old assignments in the old environment and
    preserves the new value. The equality is componentwise, not equality
    of the functions or coherence witnesses stored in semantic values. *)

(** 绑定提升在旧环境中求值旧赋值，并保持新值。这里逐分量比较，不比较语义
    值中保存的函数或相容性见证本身。 *)

Lemma eval_sub_lift {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (Θ : Ctx B) (γ : EnvF Δ Θ) (a : SemF A Θ)
  : EvalSubN (Γ ▻ A) (Δ ▻ A) (σ^↑Sub) Θ (γ, a) ≈S
      (EvalSubN Γ Δ σ Θ γ, a).
Proof.
  apply env_ext. intros U [x | x].
  - etransitivity; [apply eval_sub_lookup |].
    change (eval (σ U x)⟨wkRen⟩ Θ (γ, a) ≈S
      EnvLookupN Γ U x Θ (EvalSubN Γ Δ σ Θ γ)).
    etransitivity; [apply eval_rename |].
    etransitivity.
    + apply eval_proper. apply env_renaming_weaken.
    + symmetry. apply eval_sub_lookup.
  - destruct x. etransitivity; [apply eval_sub_lookup |]. reflexivity.
Defined.

(** Evaluating after simultaneous substitution agrees with evaluating in
    the environment of evaluated assignments. In the lambda case this
    statement is used at every future world; naturality transports the
    entire substituted environment together before adding the argument. *)

(** 先作同时替换再求值，等于在各赋值求值组成的环境中求值。λ 情形在每个
    未来世界使用此断言；自然性先整体输运替换环境，再加入实参。 *)

Lemma eval_subst {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ (Δ Θ : Ctx B) (σ : Sub Δ Γ) (γ : EnvF Δ Θ),
      eval t[σ] Θ γ ≈S eval t Θ (EvalSubN Γ Δ σ Θ γ).
Proof.
  induction t as [Γ A x | Γ | Γ A U t IHt u IHu |
    Γ A U t IH | Γ A U t IH | Γ A U t IH |
    Γ A U f IHf a IHa]; intros Δ Θ σ γ.
  - symmetry. apply eval_sub_lookup.
  - exact tt.
  - split; [apply IHt | apply IHu].
  - exact (@func_proper _ _
      (PointwiseFstN _ _ (SemF A) (SemF U) Θ) _ _ (IH Δ Θ σ γ)).
  - exact (@func_proper _ _
      (PointwiseSndN _ _ (SemF A) (SemF U) Θ) _ _ (IH Δ Θ σ γ)).
  - intros Ξ τ a.
    change (eval t[σ^↑Sub] Ξ (fmap (EnvF Δ) τ γ, a) ≈S
      eval t Ξ (fmap (EnvF Γ) τ (EvalSubN Γ Δ σ Θ γ), a)).
    etransitivity; [apply IH |]. apply eval_proper.
    etransitivity; [apply eval_sub_lift |]. split.
    + exact (nt_naturality (EvalSubN Γ Δ σ) τ γ).
    + reflexivity.
  - apply kripke_eval_proper; [apply IHf | apply IHa].
Defined.

(** Evaluating a composite substitution is successive evaluation of its
    environment maps. This is natural equality in the presheaf category. *)

(** 求值复合替换，等于依次作用其环境映射。这里使用预层范畴中的自然相等。 *)

Lemma eval_sub_comp {Γ Δ Θ : Ctx B}
    (σ : Sub Δ Γ) (τ : Sub Θ Δ)
  : EvalSubN Γ Θ (σ ∘Sub τ) ≈N
      (EvalSubN Γ Δ σ ∘Nv EvalSubN Δ Θ τ).
Proof.
  intros Ξ γ. apply env_ext. intros A x.
  etransitivity; [apply eval_sub_lookup |].
  etransitivity; [apply eval_subst |].
  symmetry. apply eval_sub_lookup.
Defined.

(** Extending a substitution appends the value of its new assignment. *)

(** 扩张替换时，附加其新赋值的值。 *)

Lemma eval_sub_extend {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (t : Tm Δ A) (Θ : Ctx B) (γ : EnvF Δ Θ)
  : EvalSubN (Γ ▻ A) Δ (σ ▻Sub t) Θ γ ≈S
      (EvalSubN Γ Δ σ Θ γ, eval t Θ γ).
Proof.
  apply env_ext. intros U [x | x].
  - etransitivity; [apply eval_sub_lookup |].
    symmetry. apply eval_sub_lookup.
  - destruct x. etransitivity; [apply eval_sub_lookup |]. reflexivity.
Defined.

(** Single substitution evaluates a body in the environment extended by
    its evaluated argument. This is the syntax-facing form of beta. *)

(** 单变量替换在按实参求值结果扩张的环境中求值项体。这是面向语法的 β 形式。 *)

Lemma eval_single {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) (u : Tm Γ A)
    (Θ : Ctx B) (γ : EnvF Γ Θ)
  : eval t[u/] Θ γ ≈S eval t Θ (γ, eval u Θ γ).
Proof.
  etransitivity; [apply eval_subst |]. apply eval_proper.
  etransitivity; [apply eval_sub_extend |]. split.
  - exact (eval_sub_id Γ Θ γ).
  - reflexivity.
Defined.

(** The syntactic function beta equation is valid in every semantic
    environment, for open terms and at arbitrary simple types. *)

(** 语法中的函数 β 方程在每个语义环境中成立，允许开放项与任意简单类型。 *)

Lemma eval_function_β {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) (u : Tm Γ A)
    (Θ : Ctx B) (γ : EnvF Γ Θ)
  : eval ((ƛ t) · u) Θ γ ≈S eval t[u/] Θ γ.
Proof.
  transitivity (eval t Θ (γ, eval u Θ γ)).
  - exact (eval_lam_β t Θ γ (eval u Θ γ)).
  - symmetry. exact (eval_single t u Θ γ).
Defined.

End EvaluationSubstitution.
