From Cats Require Export
  Cat.Terminal
  Cat.Product.Core
  Cat.Monoidal.CartesianLifting.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Applicative Endofunctors with Pure Values

    Chosen finite products supply the monoidal structure. A natural pure
    map preserves its unit and binary combination. Lax coherence is
    inherited, with no exponential objects or arbitrary chosen strength. *)

(** * 带纯值的 Applicative 自函子

    选定有限积提供幺半结构，自然纯值映射保持其单位和二元组合。Lax 相干律
    从父结构继承，不要求指数对象，也不为任意函子选取强度。 *)

(** Reserve both pure forms. The pure field locally binds its notation
    for subsequent laws; public interpretations follow the declarations. *)

(** 预留两种纯值语法。纯值字段为后续定律局部绑定记号；公共解释仍在声明后绑定。 *)

Declare Scope applicative_scope.
Delimit Scope applicative_scope with applicative.
Reserved Notation "'pure[' A ']'" (at level 0).
Reserved Notation "'pure[' A ';' x ']'" (at level 0).
Local Open Scope applicative_scope.

Record Applicative (C : Cat)
    (HT : HasTerminal C) (HP : HasProduct C)
  := ApplicativeOfLaxMonoidalFct

  (** The unique parent retains the supplied cartesian lax endofunctor. *)

  (** 唯一父结构保留给定的笛卡尔 lax 自函子。 *)

  { ApplicativeToLaxMonoidalFct
    :> LaxMonoidalFct
        (@CartMonoidal C HT HP)
        (@CartMonoidal C HT HP)

  (** Pure values commute with ordinary maps. *)

  (** 纯值与通常映射交换。 *)

  ; applicative_pure
    : IdF ⇒ ApplicativeToLaxMonoidalFct
    where "'pure[' X ']'" := (applicative_pure X)
      : applicative_scope

  (** The pure terminal value is the chosen lax unit comparison. *)

  (** 纯终值就是选定的 lax 单位比较。 *)

  ; applicative_pure_unit
    : pure[1] ≈ φ₀[ApplicativeToLaxMonoidalFct]

  (** Combining two pure values gives their pure pair. *)

  (** 组合两个纯值，得到其配对的纯值。 *)

  ; applicative_pure_product (X Y : @Ob C)
    : pure[X × Y]
      ≈ φ₂[ApplicativeToLaxMonoidalFct; X; Y]
        ∘ (pure[X] × pure[Y])
  }.

Arguments ApplicativeOfLaxMonoidalFct {_ _ _} _ _ _ _.
Arguments ApplicativeToLaxMonoidalFct {_ _ _} _.
Arguments applicative_pure {_ _ _} _.
Arguments applicative_pure_unit {_ _ _} _.
Arguments applicative_pure_product {_ _ _} _ _ _.

Notation "'pure[' A ']'" := (applicative_pure A)
  : applicative_scope.

(** Embed an ordinary value in any shared context. *)

(** 在任意共同上下文中嵌入通常值。 *)

Definition applicative_pure_value {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C}
    (A : Applicative C HT HP) {W X : @Ob C}
    (x : Hom W X)
  : Hom W (A X)
  := pure[A] X ∘ x.

Notation "'pure[' A ';' x ']'" :=
  (applicative_pure_value A x)
  : applicative_scope.

(** Pure embedding preserves the specified equality of contextual values. *)

(** 纯值嵌入保持上下文值的指定相等。 *)

Global Instance applicative_pure_value_proper
    {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C}
    (A : Applicative C HT HP) {W X : @Ob C}
  : Proper (HomEq ==> HomEq)
      (@applicative_pure_value C HT HP A W X).
Proof. intros x y H.
  unfold applicative_pure_value.
  rewrite H. reflexivity.
Qed.

(** ** Pure Values and Binary Lifting

    Fix an Applicative on selected finite products. Derive naturality, unit
    and partial-evaluation equations without any closedness assumption. *)

(** ** 纯值与二元提升

    固定选定有限积上的 Applicative，导出自然性、单位及部分求值方程，不假设闭性。 *)

Section Laws.
Context {C : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Applicative C HT HP).

(** Naturality is the ordinary-map law for pure values. *)

(** 自然性就是纯值的通常映射定律。 *)

Lemma applicative_pure_natural {X Y : @Ob C}
    (f : Hom X Y)
  : pure[A] Y ∘ f ≈ fmap A f ∘ pure[A] X.
Proof. exact (nat_naturality (pure[A]) f). Qed.

(** Lifting an operation over two pure inputs preserves its result. *)

(** 对两个纯输入提升运算，保持其结果。 *)

Lemma applicative_lift2_pure {X Y Z : @Ob C}
    (f : Hom (X × Y) Z)
  : lift₂[A; f] ∘ (pure[A] X × pure[A] Y)
    ≈ pure[A] Z ∘ f.
Proof.
  unfold lax_lift2.
  rewrite comp_assoc,
    <- (applicative_pure_product A X Y).
  symmetry. apply applicative_pure_natural.
Qed.

(** The terminal pure input on the left can be removed. *)

(** 左侧的纯终输入可以移去。 *)

Lemma applicative_unit_l (X : @Ob C)
  : lift₂[A; (π2 : Hom (1 × X) X)] ∘ (pure[A] 1 × id)
    ≈ π2.
Proof.
  unfold lax_lift2. rewrite (applicative_pure_unit A).
  pose proof (lax_unit_l A X) as H.
  rewrite cartesian_tensor_map in H. exact H.
Qed.

(** The terminal pure input on the right can be removed. *)

(** 右侧的纯终输入可以移去。 *)

Lemma applicative_unit_r (X : @Ob C)
  : lift₂[A; (π1 : Hom (X × 1) X)] ∘ (id × pure[A] 1)
    ≈ π1.
Proof.
  unfold lax_lift2. rewrite (applicative_pure_unit A).
  pose proof (lax_unit_r A X) as H.
  rewrite cartesian_tensor_map in H. exact H.
Qed.

(** A fixed pure left input reduces lifting to an ordinary unary map.
    The hypothesis states the original operation's partial evaluation. *)

(** 固定左侧纯输入后，提升归约为通常一元映射；前提说明原运算的部分求值。 *)

Lemma applicative_lift2_pure_l {X Y Z : @Ob C}
    (f : Hom (X × Y) Z) (x : Hom 1 X) (g : Hom Y Z)
    (H : f ∘ (x × id) ≈ g ∘ π2)
  : lift₂[A; f] ∘ ((pure[A] X ∘ x) × id)
    ≈ fmap A g ∘ π2.
Proof.
  rewrite (applicative_pure_natural x).
  assert (K : (fmap A x ∘ pure[A] 1) × id ≈
      (fmap A x × fmap A (id[Y])) ∘ (pure[A] 1 × id)).
  { rewrite fct_id, <- cross_comp, comp_id_l.
    reflexivity. }
  rewrite K, <- comp_assoc,
    (cartesian_lift2_pre A f x id).
  transitivity (lift₂[A; g ∘ (π2 : Hom (1 × Y) Y)]
    ∘ (pure[A] 1 × id)).
  - apply comp_proper; [| reflexivity].
    unfold lax_lift2. apply comp_proper;
      [exact (@fct_fmap_proper C C A _ _ _ _ H)
      | reflexivity].
  - rewrite <- (lax_lift2_post A (π2 : Hom (1 × Y) Y) g),
    comp_assoc, (applicative_unit_l Y). reflexivity.
Qed.

(** A fixed pure right input similarly reduces to partial evaluation. *)

(** 固定右侧纯输入后，同样归约为部分求值。 *)

Lemma applicative_lift2_pure_r {X Y Z : @Ob C}
    (f : Hom (X × Y) Z) (y : Hom 1 Y) (g : Hom X Z)
    (H : f ∘ (id × y) ≈ g ∘ π1)
  : lift₂[A; f] ∘ (id × (pure[A] Y ∘ y)) ≈ fmap A g ∘ π1.
Proof.
  rewrite (applicative_pure_natural y).
  assert (K : id × (fmap A y ∘ pure[A] 1) ≈
      (fmap A (id[X]) × fmap A y) ∘ (id × pure[A] 1)).
  { rewrite fct_id, <- cross_comp, comp_id_l. reflexivity. }
  rewrite K, <- comp_assoc, (cartesian_lift2_pre A f id y).
  transitivity
    (lift₂[A; g ∘ (π1 : Hom (X × 1) X)] ∘ (id × pure[A] 1)).
  - apply comp_proper; [| reflexivity].
    unfold lax_lift2. apply comp_proper;
      [exact (@fct_fmap_proper C C A _ _ _ _ H) | reflexivity].
  - rewrite <- (lax_lift2_post A (π1 : Hom (X × 1) X) g),
      comp_assoc, (applicative_unit_r X). reflexivity.
Qed.

End Laws.
