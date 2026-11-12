From Cats Require Export
  STLC.Product
  STLC.Packing.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Transport.

(** * Exponentials in the Syntactic Context Category

    Function beta/eta first gives the universal property for singleton
    contexts. Context packing then transports it to arbitrary contexts. *)

(** * 语法上下文范畴中的指数对象

    函数 βη 先给出单变量上下文的泛性质；上下文打包再将其运输到任意上下文。 *)

(** ** Abstraction as the unique mediator

    For singleton contexts, a map with one extra input is represented by
    an open term. Lambda abstraction constructs its function-valued
    mediator. Function beta proves that evaluation returns the original
    map, and function eta shows that any mediator with this evaluation
    behavior is beta/eta equal to the chosen one.

    For arbitrary contexts [Γ] and [Δ], [CtxExp Δ Γ] stores one function
    from [CtxTy Γ] to [CtxTy Δ]. Evaluation packs the argument block,
    applies that function and unpacks the result. Rather than repeating
    the singleton proof, the general exponential transport theorem carries
    its universal property along the packing isomorphisms. The equality
    needed for uniqueness remains pointwise beta/eta throughout. *)

(** ** 抽象是唯一的中介

    对单变量上下文，多一个输入的映射由开放项表示。λ 抽象构造函数值中介，
    函数 β 证明求值恢复原映射，函数 η 则说明：具有同样求值行为的任意中介
    都与所选中介 βη 相等。

    对任意上下文 [Γ] 与 [Δ]，[CtxExp Δ Γ] 存储一个从 [CtxTy Γ] 到
    [CtxTy Δ] 的函数。求值先打包参数块，再应用函数，最后拆包结果。
    实现没有重复单变量证明，而是沿打包同构使用一般指数运输定理传递泛性质。
    全程的唯一性都使用逐点 βη 相等。 *)

Local Open Scope stlc_ty_scope.
(** ** What beta and eta contribute separately

    An exponential must solve the problem of arrows with an extra argument,
    not merely provide a function-type object. Given such an arrow,
    abstraction supplies its curry. Applying that curry to the extra input
    recovers the original arrow by function beta. If a second candidate
    has the same evaluation behavior, function eta expresses it as the
    abstraction of that behavior and proves it equal to the first candidate.

    Thus beta establishes the mediator equation and eta establishes
    mediator uniqueness. The transport theorem then moves this full
    property along packing isomorphisms; it does not only transport an
    evaluation operation. This is the reusable categorical argument behind
    exponentials for arbitrary context blocks. *)

(** ** β 与 η 分别贡献什么

    指数必须解决带一个额外参数的箭头问题，不能只提供函数类型对象。给定
    这样的箭头，抽象构造其 curry；将 curry 应用于额外输入，函数 β 恢复原
    箭头。若第二个候选具有相同求值行为，函数 η 把它写成该行为的抽象，从而
    证明它与第一个候选相等。

    因此，β 建立中介方程，η 建立中介唯一性。运输定理随后沿打包同构移动这个
    完整性质，而不只运输求值操作。这就是任意上下文块的指数所复用的范畴论证。 *)

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

(** ** Exponentials in the Syntactic Category

    Fix base types [B] and enable the context category's chosen products.
    Prove the singleton function context represents evaluation, then extend
    the construction to arbitrary contexts. *)

(** ** 语法范畴中的指数对象

    固定基类型 [B] 并启用上下文范畴的选定积，证明单元素函数上下文表示求值，再将构造扩展到任意上下文。 *)

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
