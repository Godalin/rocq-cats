From Cats Require Export STLC.CCC.
From Cats Require Import
  Cat.Induced
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC.

(** * The Type Presentation of the Syntactic Category

    Objects are simple types, and arrows are singleton-context substitutions.
    Products and functions represent the syntax constructors directly. *)

(** * 语法范畴的类型呈现

    对象为简单类型，箭头为单变量上下文替换；积与指数直接表示语法构造器。 *)

(** ** A presentation with literal type constructors

    [CtxCat] is convenient for multiple inputs, but its objects are lists
    of types. [TyCat] restricts it along singleton contexts, using the
    general induced-category construction. Thus an arrow from [A] to [U]
    is a substitution from the singleton context of [A] to that of [U];
    its newest component is an open term of type [U] with one [A]-input.

    The chosen objects can now be the literal types [⊤], [A × U] and
    [A ⇒ U]. Product mediators pair the newest components, and function
    objects inherit the previously proved exponential property after
    comparing a pair of variables with one product variable. This changes
    presentation without constructing a new equational relation or
    repeating the function-eta uniqueness proof. *)

(** ** 以字面类型构造器呈现

    [CtxCat] 便于处理多输入，但其对象是类型列表。[TyCat] 沿单变量上下文
    使用通用的诱导范畴构造进行限制。因此，从 [A] 到 [U] 的箭头就是从 [A]
    的单变量上下文到 [U] 的单变量上下文的替换；其最新分量是一个具有单个
    [A] 输入、结果类型为 [U] 的开放项。

    这样，选定对象就能使用字面类型 [⊤]、[A × U] 和 [A ⇒ U]。积中介配对
    最新分量；函数对象先比较两个变量与一个积变量，再继承已有的指数泛性质。
    这改变了呈现方式，没有另造等式关系，也没有重复函数 η 的唯一性证明。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_var_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_sub_scope.

(** Restrict the context category along singleton contexts. *)

(** 沿单变量上下文限制上下文范畴。 *)

Definition TyCat@{b e l +} (B : Type@{b})
  : Cat@{b b e l l}
  := @InducedCat (CtxCat@{b e l} B) (Ty B) (λ A, ∅ ▻ A).

(** A unit-type context is terminal by the unit eta equation. *)

(** 单位类型的上下文由单位 η 方程给出终对象。 *)

Program Definition TyCat_HasTerminal@{b e l +} (B : Type@{b})
  : HasTerminal (TyCat@{b e l} B)
  :=
  {|Term := ty_unit
  |}.
Next Obligation.
  intros A. exists (sub_empty ▻Sub tm_unit).
  refine {|this := I
         ; that := _
         |}.
  intros σ _ U [x | x]; [destruct x | destruct x].
  apply tm_eq_unit_η.
Defined.

(** Pair the newest components to represent the product-type context.
    This property holds for every source context, not just singleton ones. *)

(** 配对最新分量，表示积类型上下文；此泛性质对任意源上下文成立。 *)

Definition singleton_product@{b e l +} {B : Type@{b}} (A U : Ty B)
  : @is_product (CtxCat@{b e l} B) (∅ ▻ A) (∅ ▻ U) (∅ ▻ (A × U))
      (sub_empty ▻Sub π₁ (# 𝟘)) (sub_empty ▻Sub π₂ (# 𝟘)).
Proof.
  intros Γ f g. exists (sub_empty ▻Sub ⟨f A 𝟘, g U 𝟘⟩).
  refine {|this := _
         ; that := _
         |}.
  - split; intros V [x | x]; [destruct x | destruct x | destruct x | destruct x];
      cbn; [apply tm_eq_product_β1 | apply tm_eq_product_β2].
  - intros h [H1 H2]. specialize (H1 A 𝟘). specialize (H2 U 𝟘).
    intros V [x | x]; [destruct x | destruct x]. cbn in *.
    transitivity (⟨π₁ (h (A × U) 𝟘), π₂ (h (A × U) 𝟘)⟩).
    + symmetry. apply tm_eq_product_η.
    + apply tm_eq_pair; assumption.
Defined.

(** Choose syntax products, with transparent pair mediators. *)

(** 选取语法积，配对中介保持透明。 *)

Program Definition TyCat_HasProduct@{b e l +} (B : Type@{b})
  : HasProduct (TyCat@{b e l} B)
  :=
  {|Prod := ty_prod
  ; π1 A U := sub_empty ▻Sub tm_fst (tm_var var_zero)
  ; π2 A U := sub_empty ▻Sub tm_snd (tm_var var_zero)
  ; product_universal A U Z := singleton_product A U (∅ ▻ Z)
  |}.

(** Encode a pair of variables into a single product variable. *)

(** 将两个变量编码为一个积类型变量。 *)

Definition type_pair_sub {B : Type} (Z A : Ty B)
  : Sub ((∅ ▻ Z) ▻ A) (∅ ▻ (Z × A))
  := sub_empty ▻Sub ⟨# (↑v 𝟘), # 𝟘⟩.

(** Decode the single product variable into the two-variable context. *)

(** 将单个积变量拆为两个变量的上下文。 *)

Definition type_split_sub {B : Type} (Z A : Ty B)
  : Sub (∅ ▻ (Z × A)) ((∅ ▻ Z) ▻ A)
  := (sub_empty ▻Sub π₁ (# 𝟘)) ▻Sub π₂ (# 𝟘).

(** The pair encoding and decoding are inverse by product beta/eta. *)

(** 积 βη 方程证明配对编码与拆分互逆。 *)

Definition type_pair_iso@{b e l +} {B : Type@{b}} (Z A : Ty B)
  : ((∅ ▻ Z) ▻ A) ≅[CtxCat@{b e l} B] (∅ ▻ (Z × A)).
Proof.
  exists (type_pair_sub Z A), (type_split_sub Z A). split.
  - intros U [[x | x] | x];
      [destruct x | destruct x | destruct x]; cbn;
      [apply tm_eq_product_β1 | apply tm_eq_product_β2].
  - intros U [x | x]; [destruct x | destruct x]. cbn.
    apply tm_eq_product_η.
Defined.

(** Splitting the product-type presentation commutes with product maps. *)

(** 拆分积类型表示与积态射交换。 *)

Lemma type_split_cross@{b e l +} {B : Type@{b}} {Z E A : Ty B}
    (h : Sub (∅ ▻ Z) (∅ ▻ E))
  : SubTmEq@{b e _}
      (type_split_sub E A ∘Sub
        @cross (TyCat@{b e l} B) (TyCat_HasProduct B)
          Z A E A h sub_id)
      (@cross (CtxCat@{b e l} B) (CtxCat_HasProduct B)
          (∅ ▻ Z) (∅ ▻ A) (∅ ▻ E) (∅ ▻ A) h sub_id
        ∘Sub type_split_sub Z A).
Proof.
  rewrite !cross_η.
  intros V [[x | x] | x]; [destruct x | destruct x | destruct x]; cbn.
  - transitivity ((h E 𝟘)[sub_empty ▻Sub (@tm_fst B (∅ ▻ (Z × A)) Z A (# 𝟘))]).
    + apply tm_eq_product_β1.
    + apply tm_eq_of_eq. unfold sub_comp.
      rewrite subst_ren, subst_rename.
      apply subst_ext. intros U [x | x]; [destruct x | destruct x].
      reflexivity.
  - apply tm_eq_product_β2.
Qed.

(** Function types inherit their full exponential property from the context
    presentation, using the product comparison rather than repeating eta. *)

(** 函数类型通过积比较继承上下文呈现的完整指数泛性质，不重复证明函数 η。 *)

Definition type_exponential@{b e l +} {B : Type@{b}} (A U : Ty B)
  : @is_exponential (TyCat@{b e l} B) (TyCat_HasProduct B)
      A U (A ⇒ U)
      (singleton_eval A U ∘Sub type_split_sub (A ⇒ U) A).
Proof.
  intros Z f.
  destruct (@singleton_exponential@{b e l _ _} B A U (∅ ▻ Z)
    (f ∘Sub type_pair_sub Z A)) as [h [Hh Hu]].
  exists h.
  refine {|this := _
         ; that := _
         |}.
  - change (SubTmEq
      ((singleton_eval A U ∘Sub type_split_sub (A ⇒ U) A) ∘Sub
        @cross (TyCat@{b e l} B) (TyCat_HasProduct B)
          Z A (A ⇒ U) A h sub_id) f).
    rewrite sub_comp_tm_assoc, type_split_cross, <- sub_comp_tm_assoc, Hh.
    assert (Hp : SubTmEq@{b e _}
      (type_pair_sub Z A ∘Sub type_split_sub Z A) sub_id).
    { exact (snd (type_pair_iso Z A).2.2). }
    rewrite sub_comp_tm_assoc, Hp, sub_comp_tm_id_r.
    reflexivity.
  - intros k Hk. apply Hu.
    change (SubTmEq
      (singleton_eval A U ∘Sub
        @cross (CtxCat@{b e l} B) (CtxCat_HasProduct B)
          (∅ ▻ Z) (∅ ▻ A) (∅ ▻ (A ⇒ U)) (∅ ▻ A) k sub_id)
      (f ∘Sub type_pair_sub Z A)).
    transitivity ((singleton_eval A U ∘Sub
      (type_split_sub (A ⇒ U) A ∘Sub
        @cross (TyCat@{b e l} B) (TyCat_HasProduct B)
          Z A (A ⇒ U) A k sub_id)) ∘Sub type_pair_sub Z A).
    + rewrite type_split_cross, <- !sub_comp_tm_assoc.
      assert (Hp : SubTmEq@{b e _}
        (type_split_sub Z A ∘Sub type_pair_sub Z A) sub_id).
      { exact (fst (type_pair_iso Z A).2.2). }
      rewrite sub_comp_tm_assoc, Hp, sub_comp_tm_id_r.
      reflexivity.
    + rewrite <- sub_comp_tm_assoc, Hk. reflexivity.
Defined.

(** Select the inherited function-type exponentials. *)

(** 选取继承得到的函数类型指数。 *)

Program Definition TyCat_HasExponential@{b e l +} (B : Type@{b})
  : HasExponential (TyCat_HasProduct@{b e l} B)
  :=
  {|exp U A := ty_arr A U
  ; eval A U := singleton_eval A U ∘Sub type_split_sub (A ⇒ U) A
  ; exponential_universal A U := type_exponential A U
  |}.

(** The type presentation is a CCC with the literal syntax constructors. *)

(** 类型呈现以语法构造器本身形成 CCC。 *)

Program Definition TyCat_CCC@{b e l +} (B : Type@{b})
  : CCC (TyCat@{b e l} B)
  :=
  {|hasTerminal := TyCat_HasTerminal B
  ; hasProduct := TyCat_HasProduct B
  ; hasExponential := TyCat_HasExponential B
  |}.
