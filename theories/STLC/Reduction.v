From Cats Require Export STLC.Equivalence.
From Cats.Set.Relation Require Import
  Congruence
  SumClosure.

(** * Contextual Reduction and Beta/Eta Convertibility

    Beta contraction, eta expansion and the unit equation remain separate
    rule sets. Their tagged sum combines alternatives, not consecutive
    reductions. A contextual step changes one generating occurrence under
    any term constructor, including abstraction. Finite zig-zags then
    recover the existing beta/eta equality without changing its definition.

    These are full contexts, not weak evaluation contexts. The generic
    congruence theorem needs preservation by every constructor, including
    binders and both arguments of binary constructors. A weak strategy
    omits some of these hypotheses and cannot simply replace this step
    relation in the argument.

    No normalization claim is made for the combined relation: unrestricted
    eta expansion can continue indefinitely, and the unit rule includes
    the loop from the unit term to itself. Beta remains independently
    available for subsequent normalization research.

    Syntax and operation labels use the signature bound [b]. Derivations
    use a separate bound [e] containing [b], including both [b < e] and
    equal-level instances. No quotient, witness irrelevance or function
    extensionality is used to discard their data. *)

(** * 上下文归约与 βη 可转换性

    β 收缩、η 展开和单位方程保持为独立规则集。其带标签和组合备选规则，而非
    连续归约。上下文步骤在任意项构造器下改变一个生成位置，包括抽象之下。
    随后的有限之字路径恢复既有 βη 相等，不改变其定义。

    这里使用完整上下文，不是弱求值上下文。一般合同定理需要每个构造器都保持
    关系，包括绑定与二元构造器的两侧。弱策略省略其中部分假设，不能在这个
    论证中直接替换步骤关系。

    不对组合关系断言正规化：无限制 η 展开可以持续进行，单位规则还包含单位项
    到自身的环。β 保持可独立使用，供后续正规化研究。

    语法与操作标签使用签名界 [b]，推导另用容纳 [b] 的界 [e]，既涵盖 [b < e]，
    也涵盖同层实例。不使用商、见证无关性或函数外延性来丢弃其中数据。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** A judgement's index records its context and result type. *)

(** 判断的索引记录其上下文与结果类型。 *)

Definition TmIndex@{b} (B : Type@{b})
  : Type@{b}
  := (Ctx B * Ty B)%type.

(** The carrier at a judgement is exactly its intrinsically typed terms. *)

(** 判断处的载体恰好是该判断的内在类型化项。 *)

Definition TmAt@{b} {B : Type@{b}} (i : TmIndex B)
  : Type@{b}
  := Tm (fst i) (snd i).

(** A relation varying with context and type. Public specializations expose
    these indices as implicit arguments. *)

(** 随上下文与类型变化的项关系。公开专化将这些索引暴露为隐含参数。 *)

Definition TmRelation@{b e +} (B : Type@{b})
  : Type
  := ∀ (Γ : Ctx B) (A : Ty B), Tm Γ A → Tm Γ A → Type@{e}.

(** Expose the same relation as an indexed family, without any transport. *)

(** 将同一关系呈现为索引族，不作任何运输。 *)

Definition tm_relation_family {B : Type} (R : TmRelation B)
  : RelationFamily (@TmAt B)
  := λ i, @R (fst i) (snd i).

(** Each operation has one varying argument. A binary operation's label
    stores its other argument; abstraction changes the source context. *)

(** 每个操作只有一个变化参数。二元操作的标签保存另一参数；抽象改变源上下文。 *)

Inductive TmOperation@{b} {B : Type@{b}}
  : TmIndex B → TmIndex B → Type@{b}
  :=| op_pair_l {Γ A U} (u : Tm Γ U)
        : TmOperation (Γ, A) (Γ, A × U)
    | op_pair_r {Γ A U} (t : Tm Γ A)
        : TmOperation (Γ, U) (Γ, A × U)
    | op_fst {Γ A U} : TmOperation (Γ, A × U) (Γ, A)
    | op_snd {Γ A U} : TmOperation (Γ, A × U) (Γ, U)
    | op_lam {Γ A U} : TmOperation (Γ ▻ A, U) (Γ, A ⇒ U)
    | op_app_l {Γ A U} (u : Tm Γ A)
        : TmOperation (Γ, A ⇒ U) (Γ, U)
    | op_app_r {Γ A U} (t : Tm Γ (A ⇒ U))
        : TmOperation (Γ, A) (Γ, U).

Arguments op_pair_l {_ _ _ _} _.
Arguments op_pair_r {_ _ _ _} _.
Arguments op_fst {_ _ _ _}.
Arguments op_snd {_ _ _ _}.
Arguments op_lam {_ _ _ _}.
Arguments op_app_l {_ _ _ _} _.
Arguments op_app_r {_ _ _ _} _.

(** Interpret operation labels by the original term constructors. An
    explicit dependent return keeps the source and target indices exact. *)

(** 用原项构造器解释操作标签。显式依赖返回类型保持源、目标索引精确。 *)

Program Definition TmContexts@{b} (B : Type@{b})
  : ContextSystem@{b b b} (@TmAt B)
  :=
  {|context_operation := TmOperation
  ; context_action i j c :=
      match c in TmOperation s t return TmAt s → TmAt t with
      | op_pair_l u => λ t, ⟨t, u⟩
      | op_pair_r t => λ u, ⟨t, u⟩
      | op_fst => λ t, π₁ t
      | op_snd => λ t, π₂ t
      | op_lam => λ t, ƛ t
      | op_app_l u => λ t, t · u
      | op_app_r t => λ u, t · u
      end
  |}.

(** Root beta contracts an introduction immediately followed by an
    elimination. It does not descend under constructors by itself. *)

(** 根 β 收缩紧随引入的消去；它本身不进入构造器内部。 *)

Inductive RootBeta@{b e +} {B : Type@{b}}
  : ∀ {Γ : Ctx B} {A : Ty B}, Tm Γ A → Tm Γ A → Type@{e}
  :=| root_beta_function {Γ A U} (t : Tm (Γ ▻ A) U) (u : Tm Γ A)
        : RootBeta ((ƛ t) · u) t[u/]
    | root_beta_fst {Γ A U} (t : Tm Γ A) (u : Tm Γ U)
        : RootBeta (π₁ ⟨t, u⟩) t
    | root_beta_snd {Γ A U} (t : Tm Γ A) (u : Tm Γ U)
        : RootBeta (π₂ ⟨t, u⟩) u.

(** Root eta points toward expansion, opposite to the orientation of the
    existing equational eta constructors. No termination is assumed. *)

(** 根 η 指向展开，与既有等式 η 构造器的方向相反；不假设终止性。 *)

Inductive RootEtaExpand@{b e +} {B : Type@{b}}
  : ∀ {Γ : Ctx B} {A : Ty B}, Tm Γ A → Tm Γ A → Type@{e}
  :=| root_eta_function {Γ A U} (f : Tm Γ (A ⇒ U))
        : RootEtaExpand f (ƛ ((f⟨wkRen⟩) · (# var_zero)))
    | root_eta_product {Γ A U} (p : Tm Γ (A × U))
        : RootEtaExpand p (⟨π₁ p, π₂ p⟩).

(** Keep the unit rule separate: its self-loop must not be included in an
    unconditional strong-normalization statement. *)

(** 单位规则保持独立：它的自环不能纳入无条件的强正规化断言。 *)

Inductive RootUnitEta@{b e +} {B : Type@{b}}
  : ∀ {Γ : Ctx B} {A : Ty B}, Tm Γ A → Tm Γ A → Type@{e}
  :=| root_unit_eta {Γ} (t : Tm Γ ⊤) : RootUnitEta t ⋆.

(** The three primitive alternatives retain their branch tags. *)

(** 三种原始备选规则保留各自的分支标签。 *)

Definition RootCombined@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, @RootBeta@{b e _} B Γ A ⊕R
      @RootEtaExpand@{b e _} B Γ A ⊕R @RootUnitEta@{b e} B Γ A.

Arguments RootCombined {_ _ _} _ _.

(** Reuse the chosen generic compatible closure. Nested contexts still
    contain exactly one original rule application, even under a binder. *)

(** 复用选定的一般相容闭包。嵌套上下文仍恰含一次原始规则应用，包括绑定之下。 *)

Definition ContextStep@{b e +} {B : Type@{b}} (R : TmRelation@{b e _} B)
    {Γ : Ctx B} {A : Ty B}
  : Tm Γ A → Tm Γ A → Type@{e}
  := CompatibleClosure (TmContexts B) (tm_relation_family R) (Γ, A).

(** Embed a primitive step at the empty single-hole context. *)

(** 将原始步骤嵌入空的单孔上下文。 *)

Definition context_step_root@{b e +} {B : Type@{b}}
    (R : TmRelation@{b e _} B) {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : R Γ A t u)
  : ContextStep R t u
  := context_step (K := TmContexts B) (R := tm_relation_family R)
      (i := (Γ, A)) h.

(** Add one constructor around a contextual step, allowing its judgement
    to change exactly as specified by the operation label. *)

(** 在上下文步骤外增加一个构造器，允许判断按操作标签的精确规定改变。 *)

Definition context_step_lift@{b e +} {B : Type@{b}}
    (R : TmRelation@{b e _} B) {Γ Δ : Ctx B} {A U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : ContextStep R t u)
  : ContextStep R (TmContexts B (Γ, A) (Δ, U) c t)
      (TmContexts B (Γ, A) (Δ, U) c u)
  := context_lift (K := TmContexts B) c h.

(** Beta steps in all contexts remain usable on their own. *)

(** 全部上下文中的 β 步骤保持可独立使用。 *)

Definition BetaStep@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, @ContextStep B (@RootBeta@{b e _} B) Γ A.

(** Eta expansion steps are likewise independent of beta and unit. *)

(** η 展开步骤同样独立于 β 和单位规则。 *)

Definition EtaExpandStep@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, @ContextStep B (@RootEtaExpand@{b e _} B) Γ A.

(** Unit steps are contextualized separately. *)

(** 单位步骤单独加入上下文。 *)

Definition UnitEtaStep@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, @ContextStep B (@RootUnitEta@{b e} B) Γ A.

(** Combine the independently available steps by the relation coproduct. *)

(** 用关系余积组合这些可独立使用的步骤。 *)

Definition CombinedStep@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, @BetaStep@{b e _ _} B Γ A ⊕R
      @EtaExpandStep@{b e _ _} B Γ A ⊕R @UnitEtaStep@{b e _} B Γ A.

Arguments BetaStep {_ _ _} _ _.
Arguments EtaExpandStep {_ _ _} _ _.
Arguments UnitEtaStep {_ _ _} _ _.
Arguments CombinedStep {_ _ _} _ _.

(** A zig-zag edge chooses a direction for one combined step. *)

(** 一条之字边为一个组合步骤选择方向。 *)

Definition ZigStep@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, (@CombinedStep@{b e _} B Γ A)^±.

Arguments ZigStep {_ _ _} _ _.

(** Empty paths and finite sequences of directed edges give convertibility. *)

(** 空路径与有限有向边序列给出可转换性。 *)

Definition ZigStar@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, @ReflTransClosure@{b e e} (Tm Γ A) (@ZigStep@{b e _ _} B Γ A).

Arguments ZigStar {_ _ _} _ _.

(** The existing equality respects every specified one-hole operation. *)

(** 既有相等保持每个指定的单孔操作。 *)

Definition tm_eq_compatible@{b e +} {B : Type@{b}}
  : is_compatible (TmContexts B) (tm_relation_family (@TmEq@{b e _} B)).
Proof.
  intros i j c. destruct c; cbn; intros x y h.
  - exact (tm_eq_pair h (tm_eq_refl u)).
  - exact (tm_eq_pair (tm_eq_refl t) h).
  - exact (tm_eq_fst h).
  - exact (tm_eq_snd h).
  - exact (tm_eq_lam h).
  - exact (tm_eq_app h (tm_eq_refl u)).
  - exact (tm_eq_app (tm_eq_refl t) h).
Defined.

(** Interpret beta generators by their existing equations. *)

(** 用既有方程解释 β 生成元。 *)

Definition root_beta_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootBeta@{b e _} t u)
  : TmEq@{b e _} t u.
Proof. destruct h.
  - exact (tm_eq_function_β t u).
  - exact (tm_eq_product_β1 t u).
  - exact (tm_eq_product_β2 t u).
Defined.

(** Eta expansion uses symmetry of the existing eta equations. *)

(** η 展开使用既有 η 方程的对称方向。 *)

Definition root_eta_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaExpand@{b e _} t u)
  : TmEq@{b e _} t u.
Proof. destruct h.
  - exact (tm_eq_sym (tm_eq_function_η f)).
  - exact (tm_eq_sym (tm_eq_product_η p)).
Defined.

(** The unit interpretation includes its harmless equational self-loop. *)

(** 单位规则的解释包含其在等式意义下无害的自环。 *)

Definition root_unit_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootUnitEta@{b e} t u)
  : TmEq@{b e _} t u.
Proof. destruct h. exact (tm_eq_unit_η t). Defined.

(** Interpret the primitive coproduct by copairing its three interpreters. *)

(** 对三个解释作余配对，得到原始余积的解释。 *)

Definition root_combined_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootCombined@{b e _} t u)
  : TmEq@{b e _} t u
  := relation_sum_case (@root_beta_to_tm_eq B Γ A)
      (relation_sum_case (@root_eta_to_tm_eq B Γ A)
        (@root_unit_to_tm_eq B Γ A)) t u h.

(** The generic context fold interprets any primitive relation whose
    generators imply the existing equality. No new context induction is
    needed for the three specializations. *)

(** 一般上下文折叠解释生成元蕴含既有相等的任意原始关系。三个专化都不需要
    新的上下文归纳。 *)

Definition context_step_to_tm_eq@{b e +} {B : Type@{b}}
    (R : TmRelation@{b e _} B)
    (hr : ∀ Γ A, @R Γ A ⊆R @TmEq@{b e _} B Γ A)
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : ContextStep R t u)
  : TmEq@{b e _} t u
  := context_closure_preserves (TmContexts B) tm_eq_compatible
      (λ i, hr (fst i) (snd i)) (Γ, A) t u h.

(** Contextualized primitive steps are again interpreted by copairing. *)

(** 加入上下文的原始步骤仍通过余配对解释。 *)

Definition combined_step_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : CombinedStep@{b e _} t u)
  : TmEq@{b e _} t u.
Proof.
  destruct h as [h | [h | h]].
  - exact (context_step_to_tm_eq _ (λ Γ A, @root_beta_to_tm_eq B Γ A) h).
  - exact (context_step_to_tm_eq _ (λ Γ A, @root_eta_to_tm_eq B Γ A) h).
  - exact (context_step_to_tm_eq _ (λ Γ A, @root_unit_to_tm_eq B Γ A) h).
Defined.

(** The sum of the three separately compatible step relations is compatible. *)

(** 三个分别相容的步骤关系之和仍然相容。 *)

Definition combined_step_compatible@{b e +} {B : Type@{b}}
  : is_compatible (TmContexts B)
      (tm_relation_family (@CombinedStep@{b e _} B)).
Proof.
  intros [Γ A] [Δ U] c x y h.
  exact (family_relation_sum_compatible (TmContexts B)
      (context_closure_compatible (TmContexts B)
        (tm_relation_family (@RootBeta@{b e _} B)))
      (family_relation_sum_compatible (TmContexts B)
        (context_closure_compatible (TmContexts B)
          (tm_relation_family (@RootEtaExpand@{b e _} B)))
        (context_closure_compatible (TmContexts B)
          (tm_relation_family (@RootUnitEta@{b e} B))))
      (Γ, A) (Δ, U) c x y h).
Defined.

(** A context around a primitive alternative maps to the corresponding
    independently contextualized step. This is the least-compatible-target
    direction of context-closure distribution over the coproduct. *)

(** 原始备选规则外部的上下文映到相应的独立上下文步骤。这是上下文闭包对余积
    分配时，由最小相容目标给出的方向。 *)

Definition root_context_to_combined_step@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ContextStep (@RootCombined@{b e _} B) t u)
  : CombinedStep@{b e _} t u.
Proof.
  refine (context_closure_preserves (TmContexts B) combined_step_compatible
    _ (Γ, A) t u h).
  intros [Δ U] x y [p | [p | p]].
  - exact (inl (context_step p)).
  - exact (inr (inl (context_step p))).
  - exact (inr (inr (context_step p))).
Defined.

(** Zig-zag equivalence is inherited from the generic equivalence closure. *)

(** 之字路径等价继承自一般等价闭包。 *)

Global Instance ZigStar_Equivalence@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B}
  : Equivalence (@ZigStar@{b e _ _} B Γ A)
  := EquivalenceClosure_Equivalence (@CombinedStep@{b e _} B Γ A).

(** Empty paths witness reflexivity. *)

(** 空路径给出自反性。 *)

Definition zig_star_refl@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ZigStar@{b e _ _} t t
  := rtc_refl t.

(** Concatenate finite paths without comparing their witnesses. *)

(** 连接有限路径，不比较路径见证。 *)

Definition zig_star_trans@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}
    (h : ZigStar@{b e _ _} t u) (k : ZigStar@{b e _ _} u v)
  : ZigStar@{b e _ _} t v
  := rtc_trans h k.

(** Reverse a path using the symmetry of its oriented edges. *)

(** 利用带方向边的对称性反转路径。 *)

Definition zig_star_sym@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : ZigStar@{b e _ _} t u)
  : ZigStar@{b e _ _} u t
  := @Equivalence_Symmetric _ _ ZigStar_Equivalence t u h.

(** The general path-lifting theorem supplies compatibility, including
    abstraction and both positions of every binary constructor. *)

(** 一般路径提升定理给出相容性，涵盖抽象以及每个二元构造器的两个位置。 *)

Definition zig_star_compatible@{b e +} {B : Type@{b}}
  : is_compatible (TmContexts B)
      (tm_relation_family (@ZigStar@{b e _ _} B))
  := family_equivalence_closure_compatible (TmContexts B)
      combined_step_compatible.

(** A single forward combined step is a one-edge path. *)

(** 一个正向组合步骤给出单边路径。 *)

Definition zig_star_step@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : CombinedStep@{b e _} t u)
  : ZigStar@{b e _ _} t u
  := rtc_step (inl h).

(** Apply the generic compatibility witness to one labeled operation. *)

(** 将一般相容性见证应用于一个带标签的操作。 *)

Definition zig_star_lift@{b e +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A U : Ty B} (c : TmOperation (Γ, A) (Δ, U))
    {t u : Tm Γ A} (h : ZigStar@{b e _ _} t u)
  : ZigStar@{b e _ _} (TmContexts B (Γ, A) (Δ, U) c t)
      (TmContexts B (Γ, A) (Δ, U) c u)
  := zig_star_compatible (Γ, A) (Δ, U) c t u h.

(** Lift under abstraction; its source context contains the bound variable. *)

(** 提升到抽象之下；源上下文包含被绑定的变量。 *)

Definition zig_star_lam@{b e +} {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}
    {t u : Tm (Γ ▻ A) U} (h : ZigStar@{b e _ _} t u)
  : ZigStar@{b e _ _} (ƛ t) (ƛ u)
  := zig_star_lift op_lam h.

(** Lift through the first projection. *)

(** 通过第一投影提升。 *)

Definition zig_star_fst@{b e +} {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}
    {t u : Tm Γ (A × U)} (h : ZigStar@{b e _ _} t u)
  : ZigStar@{b e _ _} (π₁ t) (π₁ u)
  := zig_star_lift op_fst h.

(** Lift through the second projection. *)

(** 通过第二投影提升。 *)

Definition zig_star_snd@{b e +} {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}
    {t u : Tm Γ (A × U)} (h : ZigStar@{b e _ _} t u)
  : ZigStar@{b e _ _} (π₂ t) (π₂ u)
  := zig_star_lift op_snd h.

(** Replace the left argument of a pair, retaining the right one. *)

(** 替换配对的左参数，保留右参数。 *)

Definition zig_star_pair_l@{b e +} {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}
    {t t' : Tm Γ A} (u : Tm Γ U) (h : ZigStar@{b e _ _} t t')
  : ZigStar@{b e _ _} (⟨t, u⟩) (⟨t', u⟩)
  := zig_star_lift (op_pair_l u) h.

(** Replace the right argument of a pair, retaining the left one. *)

(** 替换配对的右参数，保留左参数。 *)

Definition zig_star_pair_r@{b e +} {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ A) {u u' : Tm Γ U} (h : ZigStar@{b e _ _} u u')
  : ZigStar@{b e _ _} (⟨t, u⟩) (⟨t, u'⟩)
  := zig_star_lift (op_pair_r t) h.

(** Replace the function position of an application. *)

(** 替换应用中的函数位置。 *)

Definition zig_star_app_l@{b e +} {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}
    {t t' : Tm Γ (A ⇒ U)} (u : Tm Γ A) (h : ZigStar@{b e _ _} t t')
  : ZigStar@{b e _ _} (t · u) (t' · u)
  := zig_star_lift (op_app_l u) h.

(** Replace the argument position of an application. *)

(** 替换应用中的实参位置。 *)

Definition zig_star_app_r@{b e +} {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ (A ⇒ U)) {u u' : Tm Γ A} (h : ZigStar@{b e _ _} u u')
  : ZigStar@{b e _ _} (t · u) (t · u')
  := zig_star_lift (op_app_r t) h.

(** Interpret a reversed step by symmetry of the target equality. *)

(** 利用目标相等的对称性解释反向步骤。 *)

Definition zig_step_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : ZigStep@{b e _ _} t u)
  : TmEq@{b e _} t u
  := sym_closure_preserves (S := @TmEq@{b e _} B Γ A)
      (λ t, t) (λ t u, combined_step_to_tm_eq) h.

(** Fold a path into the existing equality using its equivalence structure. *)

(** 使用既有相等的等价结构，将路径折叠为该相等。 *)

Definition zig_star_to_tm_eq@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : ZigStar@{b e _ _} t u)
  : TmEq@{b e _} t u
  := equivalence_closure_preserves (S := @TmEq@{b e _} B Γ A)
      (λ t, t) (λ t u, combined_step_to_tm_eq) h.

(** The generic joint presentation specialized to the primitive equations.
    It shares the witness bound with the given equality and path relation. *)

(** 将一般共同呈现专化到原始方程。它与给定相等和路径关系共用见证界。 *)

Definition TmEquationalClosure@{b e +} {B : Type@{b}}
  : TmRelation@{b e _} B
  := λ Γ A, EquationalClosure (TmContexts B)
      (tm_relation_family (@RootCombined@{b e _} B)) (Γ, A).

Arguments TmEquationalClosure {_ _ _} _ _.

(** Translate the existing constructors once. Binary congruence is two
    one-hole replacements followed by transitivity; eta uses a backward
    primitive expansion. No induction over finite paths is repeated here. *)

(** 将既有构造器转换一次。二元合同由两次单孔替换及传递性组成；η 使用反向
    原始展开。这里不重复对有限路径的归纳。 *)

Definition tm_eq_to_equational_closure@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : TmEq@{b e _} t u)
  : TmEquationalClosure@{b e _} t u.
Proof.
  induction h as [Γ A t | Γ A t u p ih | Γ A t u v p ih q iq |
    Γ A U t t' u u' p ih q iq | Γ A U t u p ih | Γ A U t u p ih |
    Γ A U t u p ih | Γ A U t t' u u' p ih q iq | Γ t |
    Γ A U t u | Γ A U t u | Γ A U t | Γ A U t u | Γ A U t].
  - exact (equation_refl (i := (Γ, A)) t).
  - exact (equation_sym ih).
  - exact (equation_trans ih iq).
  - exact (equation_trans
      (equation_context (K := TmContexts B) (op_pair_l u) ih)
      (equation_context (K := TmContexts B) (op_pair_r t') iq)).
  - exact (equation_context (K := TmContexts B) op_fst ih).
  - exact (equation_context (K := TmContexts B) op_snd ih).
  - exact (equation_context (K := TmContexts B) op_lam ih).
  - exact (equation_trans
      (equation_context (K := TmContexts B) (op_app_l u) ih)
      (equation_context (K := TmContexts B) (op_app_r t') iq)).
  - exact (equation_step (i := (Γ, @ty_unit B))
      (inr (inr (root_unit_eta t)))).
  - exact (equation_step (i := (Γ, A)) (inl (root_beta_fst t u))).
  - exact (equation_step (i := (Γ, U)) (inl (root_beta_snd t u))).
  - exact (equation_sym (equation_step (i := (Γ, A × U))
      (inr (inl (root_eta_product t))))).
  - exact (equation_step (i := (Γ, U)) (inl (root_beta_function t u))).
  - exact (equation_sym (equation_step (i := (Γ, A ⇒ U))
      (inr (inl (root_eta_function t))))).
Defined.

(** Reuse the generic comparison with context paths, then map their edges
    into the sum of independently contextualized steps. *)

(** 复用与上下文路径的一般比较，再将路径边映入分别加入上下文的步骤之和。 *)

Definition tm_eq_to_zig_star@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : TmEq@{b e _} t u)
  : ZigStar@{b e _ _} t u.
Proof.
  pose (p := fst (equational_closure_paths (TmContexts B)
    (tm_relation_family (@RootCombined@{b e _} B)) (Γ, A) t u)
    (tm_eq_to_equational_closure h)).
  exact (equivalence_closure_preserves (S := @ZigStar@{b e _ _} B Γ A)
    (λ t, t) (λ t u q, rtc_step (inl (root_context_to_combined_step q))) p).
Defined.

(** The existing equality and finite full-context beta/eta zig-zags are
    the same Type-valued relation. This pair of transparent maps asserts
    neither equality nor inverse equations between derivation witnesses. *)

(** 既有相等与完整上下文中的有限 βη 之字路径是同一 Type 值关系。这对透明
    映射既不比较推导见证相等，也不为它们断言互逆方程。 *)

Definition tm_eq_zig_star@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : TmEq@{b e _} t u ↔ ZigStar@{b e _ _} t u
  := (tm_eq_to_zig_star, zig_star_to_tm_eq).
