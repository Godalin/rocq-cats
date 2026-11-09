From Cats Require Export STLC.Equivalence.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC
  Cat.Functor.Core.

(** * Interpretation in a Cartesian Closed Category

    A signature assigns an object to each base label. Environments may have
    any source object; their equality is pointwise specified hom equality.
    This keeps substitution independent of chosen context representations. *)

(** * 笛卡尔闭范畴中的解释

    签名为每个基类型标签指定对象。环境可从任意对象出发，以逐点指定 Hom 相等
    比较；因此替换定律不依赖于选定的上下文表示。 *)

(** ** From syntax operations to CCC operations

    Choose [C], its CCC structure and an object for each base label. Each
    variable becomes an arrow out of one shared source [X]. Pairing uses
    product pairing, projections use composition, abstraction uses curry,
    and application uses evaluation with paired arguments. Under a binder,
    [env_lift] changes the source to [X × TyI I A].

    The structural lemmas are proved before equational soundness. They
    describe reindexing the source, renaming variables and substituting
    terms. The beta cases of [tm_eval_sound] then use these lemmas to match
    syntactic substitution with categorical evaluation; the eta cases use
    the target universal properties. The specialized [tm_interp_sound]
    chooses the projection environment of [CtxI]. This direction applies
    to arbitrary CCC models; its converse will use the syntactic model.
    No step requires equality of semantic functions or chosen proof fields. *)

(** ** 从语法操作到 CCC 操作

    选定 [C]、其 CCC 结构以及每个基类型标签对应的对象。每个变量变成从共同
    源对象 [X] 出发的箭头。配对使用积配对，投影使用复合，抽象使用 curry，
    应用使用带配对参数的求值。绑定之下，[env_lift] 把源改为
    [X × TyI I A]。

    先于等式可靠性证明的结构引理分别处理源的预合成、变量重命名和项替换。
    [tm_eval_sound] 的 β 情形借助这些引理，把语法替换与范畴求值接起来；
    η 情形使用目标泛性质。[tm_interp_sound] 再选取 [CtxI] 的投影环境。
    这个方向适用于任意 CCC 模型，反方向随后才需要语法模型。全程不要求语义
    函数相等，也不要求选定结构的证明字段相等。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

Section Semantics.
Universes b e.
Context {B : Type@{b}} {C : Cat} `{HC : !CCC C} (I : B → @Ob C).

(** Interpret the type constructors by the selected CCC structures. *)

(** 以选定 CCC 结构解释类型构造器。 *)

Fixpoint TyI (A : Ty B)
  : @Ob C
  := match A with
  | ty_base b => I b
  | ty_unit => 1
  | ty_prod A U => (TyI A × TyI U)%ob
  | ty_arr A U => (TyI U ^ TyI A)%ob
  end.

(** An environment supplies a morphism for every typed variable. *)

(** 环境为每个带类型变量提供一条态射。 *)

Definition Env (X : @Ob C) (Γ : Ctx B)
  : Type
  := ∀ A, Var Γ A → Hom X (TyI A).

(** Compare assignments pointwise, without equality of functions. *)

(** 逐点比较赋值，不要求函数原生相等。 *)

Definition EnvEq {X Γ} (ρ τ : Env X Γ)
  : Type
  := ∀ A x, ρ A x ≈ τ A x.

(** Reindex every assignment along a context morphism. *)

(** 沿上下文态射预合成全部赋值。 *)

Definition env_comp {X Y Γ} (ρ : Env X Γ) (f : Hom Y X)
  : Env Y Γ
  := λ A x, ρ A x ∘ f.

(** Extend an environment with the newest assignment. *)

(** 用最新变量的赋值扩张环境。 *)

Definition env_extend {X Γ A} (ρ : Env X Γ) (a : Hom X (TyI A))
  : Env X (ctx_snoc Γ A)
  := λ U x, match x with
  | inl x => ρ U x
  | inr x => match x in NewVar _ V return Hom X (TyI V) with
    | new_var => a
    end
  end.

(** A binder weakens old assignments and adds the second projection. *)

(** 绑定处沿第一投影弱化旧赋值，并添加第二投影。 *)

Definition env_lift {X Γ A} (ρ : Env X Γ)
  : Env (X × TyI A)%ob (ctx_snoc Γ A)
  := env_extend (env_comp ρ π1) π2.

(** Recursive evaluation retains the computational witnesses chosen by CCC. *)

(** 递归求值保留 CCC 所选的计算见证。 *)

Fixpoint tm_eval {Γ A} (t : Tm Γ A) {X} (ρ : Env X Γ)
  : Hom X (TyI A)
  := match t in Tm Γ A return Env X Γ → Hom X (TyI A) with
  | tm_var x => λ ρ, ρ _ x
  | tm_unit => λ _, !
  | tm_pair t u => λ ρ, ⟨tm_eval t ρ, tm_eval u ρ⟩
  | tm_fst t => λ ρ, π1 ∘ tm_eval t ρ
  | tm_snd t => λ ρ, π2 ∘ tm_eval t ρ
  | tm_lam t => λ ρ, ƛ (tm_eval t (env_lift ρ))
  | tm_app t u => λ ρ, app (tm_eval t ρ) (tm_eval u ρ)
  end ρ.

(** Evaluation respects equality of all variable assignments. *)

(** 求值保持所有变量赋值的指定相等。 *)

Lemma tm_eval_ext {Γ A} (t : Tm Γ A)
  : ∀ X (ρ τ : Env X Γ), EnvEq ρ τ → tm_eval t ρ ≈ tm_eval t τ.
Proof.
  induction t; intros X ρ τ H; cbn.
  - apply H.
  - reflexivity.
  - apply product_pair_proper; auto.
  - rewrite (IHt X ρ τ H). reflexivity.
  - rewrite (IHt X ρ τ H). reflexivity.
  - apply exponential_curry_proper. apply IHt.
    intros V [x | x].
    + cbn [env_lift env_extend]. unfold env_lift, env_extend, env_comp; cbn.
      rewrite (H V x). reflexivity.
    + destruct x. reflexivity.
  - apply exponential_app_proper; auto.
Qed.

(** Evaluation commutes with reindexing the environment. *)

(** 求值与环境的预合成交换。 *)

Lemma tm_eval_comp {Γ A} (t : Tm Γ A)
  : ∀ X Y (ρ : Env X Γ) (f : Hom Y X),
      tm_eval t (env_comp ρ f) ≈ tm_eval t ρ ∘ f.
Proof.
  induction t; intros X Y ρ f; cbn.
  - reflexivity.
  - symmetry. apply term_comp_l.
  - rewrite IHt1, IHt2, product_comp_r. reflexivity.
  - rewrite IHt, comp_assoc. reflexivity.
  - rewrite IHt, comp_assoc. reflexivity.
  - transitivity (ƛ (tm_eval t (env_lift ρ) ∘ (f × id))).
    + apply exponential_curry_proper.
      transitivity (tm_eval t (env_comp (env_lift ρ) (f × id))).
      * apply tm_eval_ext. intros V [x | x]; cbn.
        -- unfold env_lift, env_extend, env_comp; cbn.
          rewrite !comp_assoc, cross_η, product_β1. reflexivity.
        -- destruct x. unfold env_lift, env_extend, env_comp; cbn.
          rewrite cross_η, product_β2, comp_id_l.
           reflexivity.
      * apply IHt.
    + apply exponential_curry_comp_r.
  - rewrite IHt1, IHt2, exponential_app_comp. reflexivity.
Qed.

(** Renaming acts by selecting the corresponding environment assignments. *)

(** 重命名通过选取对应环境赋值起作用。 *)

Lemma tm_eval_rename {Γ A} (t : Tm Γ A)
  : ∀ Δ (r : Ren Δ Γ) X (ρ : Env X Δ),
      tm_eval (rename t r) ρ ≈ tm_eval t (λ U x, ρ U (r U x)).
Proof.
  induction t; intros Δ r X ρ; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - apply exponential_curry_proper. rewrite IHt.
    apply tm_eval_ext. intros V [x | x]; reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(** Simultaneous substitution evaluates each assigned term in the same
    environment. The binder case uses renaming and reindexing, without
    functional extensionality or equality of universal-property proofs. *)

(** 同时替换在同一环境中求值每个已赋项。绑定情形使用重命名及预合成，不使用
    函数外延公理或泛性质证明相等。 *)

Lemma tm_eval_subst {Γ A} (t : Tm Γ A)
  : ∀ Δ (σ : Sub Δ Γ) X (ρ : Env X Δ),
      tm_eval (subst t σ) ρ ≈ tm_eval t (λ U x, tm_eval (σ U x) ρ).
Proof.
  induction t; intros Δ σ X ρ; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - apply exponential_curry_proper. rewrite IHt.
    apply tm_eval_ext. intros V [x | x]; cbn.
    + rewrite tm_eval_rename.
      change (tm_eval (σ V x) (env_comp ρ (π1 (X := X) (Y := TyI A))) ≈ tm_eval (σ V x) ρ ∘ π1).
      apply tm_eval_comp.
    + destruct x. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(** Every generated beta/eta equation is valid in every CCC environment. *)

(** 每条生成的 βη 方程都在任意 CCC 环境中成立。 *)

Theorem tm_eval_sound {Γ A} {t u : Tm Γ A} (H : TmEq@{b e _} t u)
  : ∀ X (ρ : Env X Γ), tm_eval t ρ ≈ tm_eval u ρ.
Proof.
  induction H; intros X ρ; cbn.
  - reflexivity.
  - symmetry. apply IHTmEq.
  - etransitivity; [apply IHTmEq1 | apply IHTmEq2].
  - rewrite IHTmEq1, IHTmEq2. reflexivity.
  - rewrite IHTmEq. reflexivity.
  - rewrite IHTmEq. reflexivity.
  - apply exponential_curry_proper. apply IHTmEq.
  - rewrite IHTmEq1, IHTmEq2. reflexivity.
  - apply term_η.
  - apply product_β1.
  - apply product_β2.
  - symmetry. apply product_η.
  - rewrite exponential_app_β, tm_eval_subst.
    transitivity (tm_eval t (env_comp (env_lift ρ)
      (⟨id, tm_eval u ρ⟩)%hom)).
    + symmetry. apply tm_eval_comp.
    + apply tm_eval_ext. intros V [x | x]; cbn.
      * unfold env_lift, env_extend, env_comp; cbn.
          rewrite comp_assoc, product_β1, comp_id_r. reflexivity.
      * destruct x. unfold env_lift, env_extend, env_comp; cbn.
          rewrite product_β2. reflexivity.
  - rewrite tm_eval_rename.
    change (ƛ (app (tm_eval t (env_comp ρ
      (π1 (X := X) (Y := TyI A)))) π2) ≈ tm_eval t ρ).
    rewrite tm_eval_comp. apply exponential_app_η.
Qed.

(** Contexts are interpreted by nested chosen products, starting at terminal. *)

(** 从选定终对象开始，以嵌套选定积解释上下文。 *)

Fixpoint CtxI (Γ : Ctx B)
  : @Ob C
  := match Γ with
  | ctx_empty => 1
  | ctx_snoc Γ A => (CtxI Γ × TyI A)%ob
  end.

(** The canonical environment consists of the context projections. *)

(** 规范环境由上下文投影组成。 *)

Fixpoint ctx_env (Γ : Ctx B)
  : Env (CtxI Γ) Γ
  := match Γ with
  | ctx_empty => λ A x, match x with end
  | ctx_snoc Γ A => env_lift (ctx_env Γ)
  end.

(** A term denotes a morphism from its interpreted context. *)

(** 项表示从其解释上下文出发的态射。 *)

Definition tm_interp {Γ A} (t : Tm Γ A)
  : Hom (CtxI Γ) (TyI A)
  := tm_eval t (ctx_env Γ).

(** Soundness uses exactly the target category's specified hom equality. *)

(** 可靠性恰好使用目标范畴指定的 Hom 相等。 *)

Theorem tm_interp_sound {Γ A} {t u : Tm Γ A} (H : TmEq@{b e _} t u)
  : tm_interp t ≈ tm_interp u.
Proof. apply tm_eval_sound. exact H. Qed.

End Semantics.

Declare Scope stlc_sem_scope.
Delimit Scope stlc_sem_scope with sem.
Notation "'⟦' A '⟧Ty[' I ']'" := (TyI I A) : stlc_sem_scope.
Notation "'⟦' Γ '⟧Ctx[' I ']'" := (CtxI I Γ) : stlc_sem_scope.
Notation "'⟦' t '⟧Tm[' I ']'" := (tm_interp I t) : stlc_sem_scope.
