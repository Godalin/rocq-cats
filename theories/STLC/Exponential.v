From Cats Require Export
  STLC.Product
  STLC.Packing.
From Cats Require Import
  Cat.Core
  Cat.Product
  Cat.Exponential
  Cat.Exponential.Transport.

(** * Exponentials in the Syntactic Context Category

    Function beta/eta first gives the universal property for singleton
    contexts. Context packing then transports it to arbitrary contexts. *)

(** * 语法上下文范畴中的指数对象

    函数 βη 先给出单变量上下文的泛性质；上下文打包再将其运输到任意上下文。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_var_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** Evaluate the two newest variables, a function and its argument. *)

(** 对最新的两个变量进行求值，它们分别为函数及其参数。 *)

Definition singleton_eval {B : Type} (A U : Ty B)
  : Sub ((∅ ▻ (A ⇒ U)) ▻ A) (∅ ▻ U)
  := sub_empty ▻Sub ((# (↑v 𝟘)) · # 𝟘).

(** Transpose a singleton-valued assignment by abstracting its newest input. *)

(** 抽象最新输入变量，将单变量值赋值转置为函数值赋值。 *)

Definition singleton_curry {B : Type} {Γ : Ctx B} {A U : Ty B}
    (f : Sub (Γ ▻ A) (∅ ▻ U))
  : Sub Γ (∅ ▻ (A ⇒ U))
  := sub_empty ▻Sub (ƛ (f U 𝟘)).

Notation "'ƛSub' f" := (singleton_curry f)
  (at level 35) : stlc_sub_scope.

(** Represent functions between arbitrary contexts by one function variable
    between their packed product types. *)

(** 用上下文积类型之间的一个函数变量，表示任意上下文间的函数。 *)

Definition CtxExp {B : Type} (Δ Γ : Ctx B)
  : Ctx B
  := ∅ ▻ (⟦Γ⟧Ty ⇒ ⟦Δ⟧Ty).

Infix "^Ctx" := CtxExp
  (at level 30, right associativity) : stlc_ctx_scope.

(** Pack the argument block, evaluate the function, then unpack the result.
    Assignment pairing makes this evaluation directly computational. *)

(** 打包参数块，对函数求值，再拆包结果；赋值配对使求值可直接计算。 *)

Definition ctx_eval {B : Type} (Γ Δ : Ctx B)
  : Sub ((Δ ^Ctx Γ) ++Ctx Γ) Δ
  := ctx_unpack_sub Δ ∘Sub singleton_eval ⟦Γ⟧Ty ⟦Δ⟧Ty ∘Sub
      ⟨RenSub (ren_append_l (Δ ^Ctx Γ) Γ),
        ctx_pack_sub Γ ∘Sub RenSub (ren_append_r (Δ ^Ctx Γ) Γ)⟩Sub.

Section SyntacticExponentials.
Universes b e l.
Context {B : Type@{b}}.
Local Instance syntactic_products
  : HasProduct (CtxCat@{b e l} B)
  := CtxCat_HasProduct B.

(** Evaluation after a product map is application of the weakened function
    to the newest variable. *)

(** 求值与积映射复合后，等于将弱化后的函数应用于最新变量。 *)

Definition singleton_eval_comp {Γ : Ctx B} {A U : Ty B}
    (h : Sub Γ (∅ ▻ (A ⇒ U)))
  : SubTmEq@{b e _}
      (singleton_eval A U ∘Sub
        @cross (CtxCat@{b e l} B) syntactic_products
          Γ (∅ ▻ A) (∅ ▻ (A ⇒ U)) (∅ ▻ A) h sub_id)
      (sub_empty ▻Sub ((h (A ⇒ U) 𝟘)⟨wkRen⟩ · # 𝟘)).
Proof.
  rewrite cross_η.
  intros V [x | x]; [destruct x | destruct x].
  cbn. unfold sub_comp. rewrite subst_ren. apply tm_eq_refl.
Defined.

(** Function beta proves the evaluation equation; function eta gives the
    uniqueness of abstraction. No equality of substitution functions is used. *)

(** 函数 β 证明求值方程，函数 η 给出抽象的唯一性；不使用替换函数相等。 *)

Definition singleton_exponential (A U : Ty B)
  : @is_exponential (CtxCat@{b e l} B) syntactic_products
      (∅ ▻ A) (∅ ▻ U) (∅ ▻ (A ⇒ U)) (singleton_eval A U).
Proof.
  intros Γ f. exists (ƛSub f).
  refine {|this := _
         ; that := _
         |}.
  - rewrite (singleton_eval_comp (ƛSub f)).
    intros V [x | x]; [destruct x | destruct x]. cbn.
    transitivity ((f U 𝟘)⟨(@ren_weaken B Γ A)^↑Ren⟩[# 𝟘/]).
    + apply tm_eq_function_β.
    + apply tm_eq_of_eq. apply rename_lift_single.
  - intros k Hk. rewrite (singleton_eval_comp k) in Hk.
    specialize (Hk U 𝟘). cbn in Hk.
    intros V [x | x]; [destruct x | destruct x]. cbn.
    transitivity (ƛ ((k (A ⇒ U) 𝟘)⟨wkRen⟩ · # 𝟘)).
    + apply tm_eq_sym. apply tm_eq_function_η.
    + apply tm_eq_lam. exact Hk.
Defined.

(** Context packing transports the singleton exponential property in its two
    endpoints. Equality of evaluations preserves the same universal mediator. *)

(** 上下文打包沿两个端点运输单变量指数泛性质；求值相等保持同一个泛中介。 *)

Definition ctx_exponential (Γ Δ : Ctx B)
  : @is_exponential (CtxCat@{b e l} B) syntactic_products
      Γ Δ (Δ ^Ctx Γ) (ctx_eval Γ Δ).
Proof.
  refine (exponential_eval_equiv
    (C := CtxCat@{b e l} B) (HP := syntactic_products)
    (ev := ctx_unpack_sub Δ ∘Sub singleton_eval ⟦Γ⟧Ty ⟦Δ⟧Ty ∘Sub
      @cross (CtxCat@{b e l} B) syntactic_products
        (Δ ^Ctx Γ) Γ (Δ ^Ctx Γ) (∅ ▻ ⟦Γ⟧Ty) sub_id (ctx_pack_sub Γ))
    _ _).
  - rewrite cross_η, comp_id_l. reflexivity.
  - exact (exponential_transport (ctx_pack_iso Γ)
      (iso_symm (ctx_pack_iso Δ)) (singleton_eval ⟦Γ⟧Ty ⟦Δ⟧Ty)
      (singleton_exponential ⟦Γ⟧Ty ⟦Δ⟧Ty)).
Defined.

End SyntacticExponentials.

(** Select the context exponentials and their transparent evaluations.
    Importing this structure does not enable it globally. *)

(** 选定上下文指数对象及其透明求值；导入本结构不会将其全局启用。 *)

Program Definition CtxCat_HasExponential@{b e l +} (B : Type@{b})
  : HasExponential (CtxCat_HasProduct@{b e l} B)
  :=
  {|exp := CtxExp
  ; eval Γ Δ := ctx_eval Γ Δ
  ; exponential_universal Γ Δ := ctx_exponential Γ Δ
  |}.
