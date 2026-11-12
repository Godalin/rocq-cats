From Cats Require Export
  STLC.Semantics
  STLC.Category.
From Cats Require Import
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC
  Cat.Functor.Core.

(** * Context Interpretation and Semantic Substitution *)

(** * 上下文解释与语义替换 *)

(** ** Why interpreting substitutions needs a tuple map

    An interpreted context is a nested product. [env_tuple] turns one arrow
    for each variable into an arrow to that product. Its beta law recovers
    each component; its eta law reconstructs a map from those components.
    These laws justify treating environments and context arrows as two
    presentations of the same semantic data up to specified equality.

    [sub_interp] tuples the interpretations of all terms assigned by a
    substitution. The term substitution theorem becomes precomposition
    with this arrow. Identity and composition then follow from the raw
    substitution algebra and tuple laws. A further soundness argument
    shows that beta/eta equal assignments have equal denotations, which is
    the respectfulness required to assemble [InterpretF] on the syntactic
    hom-setoids. Its arrow map is concrete data, not a choice from a
    Prop-only existence statement. *)

(** ** 为什么解释替换需要元组映射

    上下文的解释是嵌套积。[env_tuple] 把每个变量的一条箭头组成指向该积的
    箭头。β 律恢复各分量，η 律由这些分量重建映射。因此，环境与上下文箭头
    是同一语义数据的两种表示，并按指定相等联系。

    [sub_interp] 将替换所赋各项的解释组成元组，项替换定理就变成沿该箭头
    预合成。单位与复合随后由原始替换代数及元组定律推出。另用可靠性证明
    βη 相等赋值具有相等解释，得到组装 [InterpretF] 时所需的 Hom 广集
    保相等性。其箭头映射是具体数据，不是从 Prop 层存在性中进行选择。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

(** ** Interpreting Context Substitutions

    Fix a CCC [C] and a base-type assignment [I]. Interpret tuples and
    substitutions as arrows, prove substitution compatibility, and assemble
    the interpretation functor. *)

(** ** 解释上下文替换

    固定 CCC [C] 及基类型赋值 [I]，将元组和替换解释为箭头，证明替换相容性，并组装解释函子。 *)

Section Interpretation.
Universes b e l.
Context {B : Type@{b}} {C : Cat} `{HC : !CCC C} (I : B → @Ob C).

(** Assemble variable assignments into their representing context product. *)

(** 将变量赋值组装为其表示上下文积中的态射。 *)

Fixpoint env_tuple {X Γ} (ρ : Env I X Γ)
  : Hom X (CtxI I Γ)
  := match Γ as Γ return Env I X Γ → Hom X (CtxI I Γ) with
  | ctx_empty => λ _, !
  | ctx_snoc Γ A => λ ρ,
      ⟨env_tuple (λ U x, ρ U (var_succ x)), ρ A var_zero⟩
  end ρ.

(** Pointwise equal environments give equal tuples. *)

(** 逐点相等的环境给出相等的元组。 *)

Lemma env_tuple_ext {X Γ} (ρ τ : Env I X Γ) (H : EnvEq I ρ τ)
  : env_tuple ρ ≈ env_tuple τ.
Proof.
  induction Γ; cbn; [reflexivity |].
  apply product_pair_proper; [apply IHΓ | apply H].
  intros U x. apply H.
Qed.

(** The projections recover every assigned variable. *)

(** 投影恢复每个变量的赋值。 *)

Lemma env_tuple_β {X Γ} (ρ : Env I X Γ)
  : EnvEq I (env_comp I (ctx_env I Γ) (env_tuple ρ)) ρ.
Proof.
  induction Γ; intros U x; [destruct x |].
  destruct x as [x | x]; cbn [env_comp ctx_env env_lift env_extend].
  - unfold env_lift, env_extend, env_comp; cbn.
    rewrite comp_assoc, product_β1. apply IHΓ.
  - destruct x. unfold env_lift, env_extend, env_comp; cbn.
    apply product_β2.
Qed.

(** A map into a context is recovered from all its projections. *)

(** 指向上下文的态射由其全部投影恢复。 *)

Lemma env_tuple_η {X Γ} (f : Hom X (CtxI I Γ))
  : env_tuple (env_comp I (ctx_env I Γ) f) ≈ f.
Proof.
  induction Γ; cbn [env_tuple ctx_env env_comp env_lift env_extend].
  - symmetry. apply term_η.
  - transitivity (⟨π1 ∘ f, π2 ∘ f⟩).
    + apply product_pair_proper; [|reflexivity].
      transitivity (env_tuple (env_comp I (ctx_env I Γ) (π1 ∘ f))).
      * apply env_tuple_ext. intros U x. apply comp_assoc.
      * apply IHΓ.
    + symmetry. apply product_η.
Qed.

(** Tupling commutes with precomposition. *)

(** 元组与预合成交换。 *)

Lemma env_tuple_comp {X Y Γ} (ρ : Env I X Γ) (f : Hom Y X)
  : env_tuple (env_comp I ρ f) ≈ env_tuple ρ ∘ f.
Proof.
  induction Γ; cbn [env_tuple env_comp].
  - symmetry. apply term_comp_l.
  - etransitivity.
    + apply product_pair_proper; [apply IHΓ | reflexivity].
    + symmetry. apply product_comp_r.
Qed.

(** Interpret simultaneous substitution by tupling its interpreted terms. *)

(** 将替换所赋项的解释组成元组，得到同时替换的解释。 *)

Definition sub_interp {Γ Δ} (σ : Sub Δ Γ)
  : Hom (CtxI I Δ) (CtxI I Γ)
  := env_tuple (λ U x, tm_interp I (σ U x)).

(** A syntactic substitution becomes categorical precomposition. *)

(** 语法替换成为范畴中的预合成。 *)

Theorem tm_interp_subst {Γ A} (t : Tm Γ A) {Δ} (σ : Sub Δ Γ)
  : tm_interp I (subst t σ) ≈ tm_interp I t ∘ sub_interp σ.
Proof.
  unfold tm_interp. rewrite tm_eval_subst.
  transitivity (tm_eval I t
    (env_comp I (ctx_env I Γ) (sub_interp σ))).
  - apply tm_eval_ext. intros U x. symmetry.
    exact (env_tuple_β (λ V y, tm_interp I (σ V y)) U x).
  - apply tm_eval_comp.
Qed.

(** Pointwise beta/eta equal substitutions have equal denotations. *)

(** 逐点 βη 相等的替换具有相等解释。 *)

Lemma sub_interp_proper {Γ Δ} {σ τ : Sub Δ Γ} (H : SubTmEq@{b e _} σ τ)
  : sub_interp σ ≈ sub_interp τ.
Proof. apply env_tuple_ext. intros U x. apply tm_interp_sound. apply H. Qed.

(** The identity substitution denotes the identity morphism. *)

(** 恒等替换解释为恒等态射。 *)

Lemma sub_interp_id {Γ}
  : sub_interp (@sub_id B Γ) ≈ id.
Proof.
  transitivity (env_tuple (env_comp I (ctx_env I Γ) id)).
  - apply env_tuple_ext. intros U x. symmetry. apply comp_id_r.
  - apply env_tuple_η.
Qed.

(** Substitution composition denotes morphism composition. *)

(** 替换复合解释为态射复合。 *)

Lemma sub_interp_comp {Γ Δ Θ} (σ : Sub Δ Γ) (τ : Sub Θ Δ)
  : sub_interp (sub_comp σ τ) ≈ sub_interp σ ∘ sub_interp τ.
Proof.
  transitivity (env_tuple (env_comp I
    (λ U x, tm_interp I (σ U x)) (sub_interp τ))).
  - apply env_tuple_ext. intros U x. apply tm_interp_subst.
  - apply env_tuple_comp.
Qed.

(** The semantic substitution laws assemble the interpretation functor. *)

(** 语义替换定律组装为解释函子。 *)

Program Definition InterpretF
  : Functor (CtxCat@{b e l} B) C
  :=
  {|F0 := CtxI I
  ; F1 Γ Δ σ := sub_interp σ
  |}.
Next Obligation. intros σ τ H. apply sub_interp_proper. exact H. Qed.
Next Obligation. apply sub_interp_id. Qed.
Next Obligation. apply sub_interp_comp. Qed.

End Interpretation.
