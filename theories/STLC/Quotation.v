From Cats Require Export STLC.TypeCategory.
From Cats Require Import
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC.

(** * Evaluation in the Literal Type Presentation

    Here types are interpreted literally. This auxiliary evaluator avoids
    identifying a recursive type interpretation with the identity function. *)

(** * 字面类型呈现中的求值

    此处类型按字面解释；辅助求值器不要求递归类型解释与恒等函数原生相等。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_ren_scope.


Section Quotation.
Universes b e l.
Context {B : Type@{b}}.
Local Instance type_ccc
  : CCC (TyCat@{b e l} B)
  := TyCat_CCC B.

(** Variable assignments by arrows of the literal type category. *)

(** 以字面类型范畴中的箭头给变量赋值。 *)

Definition TyEnv (X : Ty B) (Γ : Ctx B)
  : Type
  := ∀ A, Var Γ A → (@Hom (TyCat@{b e l} B)) X A.

(** Extend a literal environment under a binder. *)

(** 在绑定处扩张字面环境。 *)

Definition ty_env_lift {X Γ A} (ρ : TyEnv X Γ)
  : TyEnv (ty_prod X A) (ctx_snoc Γ A)
  := λ U x, match x with
  | inl x => (ρ U x ∘ (@Cats.Cat.Product.Core.π1 (TyCat@{b e l} B)
      (TyCat_HasProduct B) X A))%hom
  | inr x => match x in NewVar _ V
      return (@Hom (TyCat@{b e l} B)) (ty_prod X A) V with
    | new_var => @Cats.Cat.Product.Core.π2 (TyCat@{b e l} B)
        (TyCat_HasProduct B) X A
    end
  end.

(** Evaluate the syntax using the literal terminal, product and function types. *)

(** 使用字面单位、积和函数类型对语法求值。 *)

Fixpoint syntax_eval {Γ A} (t : Tm Γ A) {X} (ρ : TyEnv X Γ)
  : (@Hom (TyCat@{b e l} B)) X A
  := match t in Tm Γ A return TyEnv X Γ → (@Hom (TyCat B)) X A with
  | tm_var x => λ ρ, ρ _ x
  | tm_unit => λ _, @term (TyCat@{b e l} B) (TyCat_HasTerminal B) X
  | tm_pair t u => λ ρ, @pair (TyCat@{b e l} B)
      (TyCat_HasProduct B) _ _ X (syntax_eval t ρ) (syntax_eval u ρ)
  | tm_fst t => λ ρ, (@Cats.Cat.Product.Core.π1 (TyCat@{b e l} B)
      (TyCat_HasProduct B) _ _ ∘ syntax_eval t ρ)%hom
  | tm_snd t => λ ρ, (@Cats.Cat.Product.Core.π2 (TyCat@{b e l} B)
      (TyCat_HasProduct B) _ _ ∘ syntax_eval t ρ)%hom
  | tm_lam t => λ ρ, @curry (TyCat@{b e l} B) (TyCat_HasProduct B)
      (TyCat_HasExponential B) _ _ X (syntax_eval t (ty_env_lift ρ))
  | tm_app t u => λ ρ, @app (TyCat@{b e l} B) (TyCat_HasProduct B)
      (TyCat_HasExponential B) _ _ X (syntax_eval t ρ) (syntax_eval u ρ)
  end ρ.

(** The chosen transpose computes by abstraction after packing its two inputs. *)

(** 选定转置按打包两个输入后再抽象进行计算。 *)

Lemma type_curry_compute {X A U : Ty B}
    (f : (@Hom (TyCat@{b e l} B)) (ty_prod X A) U)
  : (@curry (TyCat@{b e l} B) (TyCat_HasProduct B)
      (TyCat_HasExponential B) A U X f) (ty_arr A U) var_zero
      = tm_lam ((f U var_zero)[type_pair_sub X A]).
Proof. reflexivity. Qed.

(** Literal evaluation returns the original term after its assigned terms
    are substituted. Equality remains beta/eta, including under binders. *)

(** 字面求值给出用已赋项替换后的原项；相等仍为 βη，相同结论也覆盖绑定变量。 *)

Theorem syntax_eval_quote {Γ A} (t : Tm Γ A)
  : ∀ X (ρ : TyEnv X Γ), TmEq@{b e _}
      (syntax_eval t ρ A var_zero) t[λ U x, ρ U x U var_zero].
Proof.
  induction t; intros X ρ; cbn.
  - reflexivity.
  - reflexivity.
  - apply tm_eq_pair; [apply IHt1 | apply IHt2].
  - apply tm_eq_fst. apply IHt.
  - apply tm_eq_snd. apply IHt.
  - change (TmEq
      (tm_lam ((syntax_eval t (ty_env_lift ρ) U var_zero)[type_pair_sub X A]))
      (tm_lam (t[(λ V x, ρ V x V var_zero)^↑Sub]))).
    apply tm_eq_lam.
    transitivity ((t[λ V x, ty_env_lift ρ V x V var_zero])[
      type_pair_sub X A]).
    + apply tm_eq_subst. apply IHt.
    + rewrite subst_comp. apply subst_tm_ext.
      intros V [x | x]; cbn.
      * unfold sub_comp. rewrite subst_comp.
        transitivity ((ρ V x V var_zero)[
          RenSub (@ren_weaken B (ctx_snoc ctx_empty X) A)]).
        -- apply subst_tm_ext. intros W [y | y]; [destruct y | destruct y].
           cbn. apply tm_eq_product_β1.
        -- apply tm_eq_of_eq. apply subst_ren.
      * destruct x. apply tm_eq_product_β2.
  - transitivity (tm_app (syntax_eval t1 ρ _ var_zero)
      (syntax_eval t2 ρ _ var_zero)).
    + apply tm_eq_app; [apply tm_eq_product_β1 | apply tm_eq_product_β2].
    + apply tm_eq_app; [apply IHt1 | apply IHt2].
Defined.

End Quotation.

(** The literal singleton environment assigns its input variable the identity. *)

(** 字面单变量环境将输入变量赋为恒等。 *)

Definition ty_single_env@{b e l +} {B : Type@{b}} (A : Ty B)
  : TyEnv@{b e l _} A (ctx_snoc ctx_empty A)
  := λ U x, match x with
  | inl x => match x with end
  | inr x => match x in NewVar _ V
      return (@Hom (TyCat@{b e l} B)) A V with
    | new_var => sub_id
    end
  end.

(** Evaluating a singleton arrow in its identity environment recovers it. *)

(** 在恒等环境中求值单变量箭头可恢复该箭头。 *)

Theorem syntax_eval_retract@{b e l +} {B : Type@{b}} {A U : Ty B}
    (f : (@Hom (TyCat@{b e l} B)) A U)
  : @HomEq (TyCat@{b e l} B) A U
      (syntax_eval (f U var_zero) (ty_single_env A)) f.
Proof.
  intros V [x | x]; [destruct x | destruct x].
  transitivity ((f U var_zero)[λ V x, ty_single_env A V x V var_zero]).
  - apply syntax_eval_quote.
  - apply tm_eq_of_eq. transitivity ((f U var_zero)[sub_id]).
    + apply subst_ext. intros V [x | x]; [destruct x | destruct x].
      reflexivity.
    + apply subst_id.
Defined.

(** Canonical projections for the nested product representing a context. *)

(** 表示上下文的嵌套积的规范投影。 *)

Fixpoint packed_env@{b e l +} {B : Type@{b}} (Γ : Ctx B)
  : TyEnv@{b e l _} (CtxTy Γ) Γ
  := match Γ with
  | ctx_empty => λ A x, match x with end
  | ctx_snoc Γ A => ty_env_lift (packed_env Γ)
  end.

(** The literal projections agree with unpacking the product variable. *)

(** 字面投影与拆包积变量一致。 *)

Lemma packed_env_unpack@{b e l +} {B : Type@{b}} (Γ : Ctx B)
  : ∀ A x, TmEq@{b e _} (packed_env@{b e l _} Γ A x A var_zero)
      (ctx_unpack Γ (tm_var var_zero) A x).
Proof.
  induction Γ as [|Γ IH A]; intros U x; [destruct x |].
  destruct x as [x | x]; [|destruct x; reflexivity].
  pose (p := @tm_fst B (ctx_snoc ctx_empty (ty_prod (CtxTy Γ) A))
    (CtxTy Γ) A (tm_var var_zero)).
  change (TmEq ((packed_env@{b e l _} Γ U x U var_zero)[
    sub_empty ▻Sub p])
    (ctx_unpack Γ (p) U x)).
  transitivity ((ctx_unpack Γ (tm_var var_zero) U x)[
    sub_empty ▻Sub p]).
  - apply tm_eq_subst. apply IH.
  - apply tm_eq_of_eq.
    exact (ctx_unpack_subst Γ (tm_var var_zero)
      (sub_empty ▻Sub p) U x).
Defined.

(** A term becomes an arrow from the context's product type. *)

(** 项成为从上下文积类型出发的箭头。 *)

Definition quote_tm {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : Sub (ctx_snoc ctx_empty (CtxTy Γ)) (ctx_snoc ctx_empty A)
  := sub_empty ▻Sub t[ctx_unpack Γ (tm_var var_zero)].

(** The canonical literal environment gives the packed-context quotation. *)

(** 规范字面环境给出打包上下文中的项表示。 *)

Theorem syntax_eval_packed@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : SubTmEq@{b e _} (syntax_eval t (packed_env@{b e l _} Γ)) (quote_tm t).
Proof.
  intros U [x | x]; [destruct x | destruct x].
  etransitivity; [apply syntax_eval_quote |].
  apply subst_tm_ext. intros V x. apply packed_env_unpack.
Defined.

(** Quotation reflects equality, by substituting the packed identity context. *)

(** 将打包后的恒等上下文代入，证明项表示反映相等。 *)

Theorem quote_tm_faithful@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (H : SubTmEq@{b e _} (quote_tm t) (quote_tm u))
  : TmEq@{b e _} t u.
Proof.
  specialize (H A var_zero). unfold quote_tm in H; cbn in H.
  pose proof (tm_eq_subst H Γ (ctx_pack_sub Γ)) as K.
  rewrite !subst_comp in K.
  assert (Ht : TmEq@{b e _} t
    t[sub_comp (ctx_unpack Γ (tm_var var_zero)) (ctx_pack_sub Γ)]).
  { transitivity t[sub_id]; [symmetry; apply tm_eq_of_eq; apply subst_id |].
    apply subst_tm_ext. symmetry.
    transitivity (ctx_unpack Γ (ctx_pack sub_id)).
    - apply sub_tm_eq_of_eq. apply ctx_unpack_subst.
    - apply ctx_pack_β. }
  transitivity t[sub_comp (ctx_unpack Γ (tm_var var_zero)) (ctx_pack_sub Γ)];
    [exact Ht |].
  transitivity u[sub_comp (ctx_unpack Γ (tm_var var_zero)) (ctx_pack_sub Γ)];
    [exact K |].
  transitivity u[sub_id].
  - apply subst_tm_ext.
    transitivity (ctx_unpack Γ (ctx_pack sub_id)).
    + apply sub_tm_eq_of_eq. apply ctx_unpack_subst.
    + apply ctx_pack_β.
  - apply tm_eq_of_eq. apply subst_id.
Defined.
