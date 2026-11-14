From Cats Require Export
  STLC.EvaluationSubstitution.
From Cats Require Import
  STLC.Equivalence
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.FiniteProducts
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Kripke.

(** * Beta/Eta Equality in Semantic Environments

    The substitution lemma validates function beta in every environment.
    Function eta is observed at every future world, using weakening to
    discard the fresh entry and naturality to transport the function value.
    These arguments validate all generators of [TmEq] in the semantic
    setoids. This supplies the semantic equality used by normalization
    invariance in [STLC.Normalization].

    This direction compares the meanings of equal terms. It does not yet
    prove that each term is beta/eta equal to its computed normal form,
    nor that every directed reduction sequence terminates. *)

(** * 语义环境中的 βη 相等

    替换引理在每个环境中验证函数 β。函数 η 在每个未来世界进行观察，使用
    弱化丢弃新分量，再由自然性输运函数值。这些论证在语义广集中验证 [TmEq]
    的全部生成规则，为 [STLC.Normalization] 中的正规化不变性提供所需的
    语义相等。

    这个方向比较相等项的含义，尚未证明每个项与计算所得正规形 βη 相等，
    也没有证明每条有向归约序列终止。 *)

Local Existing Instance SetCat_HasProduct.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_tm_scope.

(** ** Equations in a Fixed Evaluation Model

    Fix a signature [B] and world equality, semantic and world-law bounds.
    Validate function eta and all beta/eta derivations in this model;
    equational evidence keeps a separate bound chosen by each lemma. *)

(** ** 固定求值模型中的方程

    固定签名 [B] 及世界相等、语义与世界定律界限，在此模型中验证函数 η 及
    全部 βη 推导；等式证据保留由各引理另选的独立界限。 *)

Section EvaluationEquivalence.
Universes b r s l.
Context {B : Type@{b}}.

(** Function eta holds extensionally at all future applications. The
    statement fixes the semantic bounds through the environment functor;
    it requires no native equality of semantic functions. *)

(** 函数 η 在全部未来应用处外延成立。断言通过环境函子固定语义界限，不要求
    语义函数的原生相等。 *)

Lemma eval_function_η {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ (A ⇒ U)) (Θ : Ctx B)
    (γ : (EnvF Γ : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) Θ)
  : eval (ƛ (t⟨wkRen⟩ · (# var_zero))) Θ γ ≈S eval t Θ γ.
Proof.
  intros Ξ ρ a.
  change (kripke_eval (SemF A) (SemF U)
    (eval t⟨wkRen⟩ Ξ (fmap (EnvF Γ) ρ γ, a)) a ≈S
    ((eval t Θ γ) Ξ ρ a)).
  transitivity (kripke_eval (SemF A) (SemF U)
    (fmap (SemF (A ⇒ U)) ρ (eval t Θ γ)) a).
  - apply kripke_eval_proper; [| reflexivity].
    transitivity (eval t Ξ (EnvRenamingN Γ (Γ ▻ A) wkRen Ξ
      (fmap (EnvF Γ) ρ γ, a))).
    + exact (eval_rename t (Γ ▻ A) Ξ wkRen
        (fmap (EnvF Γ) ρ γ, a)).
    + transitivity (eval t Ξ (fmap (EnvF Γ) ρ γ)).
      * exact (eval_proper t Ξ _ _
          (env_renaming_weaken Ξ (fmap (EnvF Γ) ρ γ) a)).
      * exact (eval_reindex t Θ Ξ ρ γ).
  - change ((eval t Θ γ) Ξ (ρ ∘Ren idRen) a ≈S
      (eval t Θ γ) Ξ ρ a).
    apply kripke_apply_proper; [exact (ren_comp_id_r ρ) | reflexivity].
Defined.

(** Every beta/eta derivation gives natural equality of evaluation maps.
    Its Type-valued evidence bound [e] is independent of the semantic
    bound [s]: only the source signature must fit in both. *)

(** 每个 βη 推导都给出求值映射的自然相等。Type 值证据界限 [e] 与语义界限
    [s] 独立：只要求源签名分别容纳于二者。 *)

Lemma eval_tm_eq@{e +} {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : TmEq@{b e _} t u)
  : (EvalN t : (EnvF Γ :
      Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) ⇒ SemF A) ≈N EvalN u.
Proof.
  induction h as [Γ A t | Γ A t u h IH |
    Γ A t u v h IH k IK | Γ A U t t' u u' h IH k IK |
    Γ A U t u h IH | Γ A U t u h IH |
    Γ A U t u h IH | Γ A U t t' u u' h IH k IK |
    Γ t | Γ A U t u | Γ A U t u | Γ A U t |
    Γ A U t u | Γ A U t]; intros Θ γ.
  - reflexivity.
  - symmetry. apply IH.
  - transitivity (eval u Θ γ); [apply IH | apply IK].
  - split; [apply IH | apply IK].
  - exact (@func_proper _ _
      (PointwiseFstN _ _ (SemF A) (SemF U) Θ) _ _ (IH Θ γ)).
  - exact (@func_proper _ _
      (PointwiseSndN _ _ (SemF A) (SemF U) Θ) _ _ (IH Θ γ)).
  - intros Ξ ρ a. apply IH.
  - apply kripke_eval_proper; [apply IH | apply IK].
  - exact tt.
  - reflexivity.
  - reflexivity.
  - change ((fst (eval t Θ γ), snd (eval t Θ γ)) ≈S eval t Θ γ).
    destruct (eval t Θ γ). split; reflexivity.
  - exact (eval_function_β t u Θ γ).
  - exact (eval_function_η t Θ γ).
Defined.

(** Evaluation of substitutions respects pointwise beta/eta equality of
    their assignments. Thus semantic context maps need no raw-tree
    equality of the chosen assignments. *)

(** 替换的求值保持其赋值的逐点 βη 相等。因此语义上下文映射无须所选赋值
    的原始树相等。 *)

Lemma eval_sub_tm_eq@{e +} {Γ Δ : Ctx B} {σ τ : Sub Δ Γ}
    (h : SubTmEq@{b e _} σ τ)
  : EvalSubN Γ Δ σ ≈N EvalSubN Γ Δ τ.
Proof.
  intros Θ γ. apply env_ext. intros A x.
  etransitivity; [apply eval_sub_lookup |].
  etransitivity; [exact (eval_tm_eq (h A x) Θ γ) |].
  symmetry. apply eval_sub_lookup.
Defined.

End EvaluationEquivalence.
