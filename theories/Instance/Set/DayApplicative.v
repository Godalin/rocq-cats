From Cats Require Export
  Cat.Day.Comparison
  Instance.Set.LaxApplicative.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid
  Instance.Set.Exponential.
From Cats.Set Require Import
  Constant.

Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Direct Applicatives and Day Monoids on Native Setoids

    The existing Day interfaces lift Hom weights into their value universe.
    For full native setoid endofunctors, both ambient levels therefore use
    the explicitly shared bound [u]. This specialization does not restrict
    the independent levels of [SetLaxA]. Convolutions remain supplied data;
    no full-setoid self-indexing coend or resizing principle is constructed. *)

(** * 原生广集上的直接 Applicative 与 Day 幺半群

    已有 Day 接口将 Hom 权重提升至其值宇宙；完整原生广集自函子特化因此显式
    使用共同环境界 [u]。此特化不限制 [SetLaxA] 的独立层级。卷积仍由输入给定，
    不构造全广集自索引 coend，也不引入 resizing 原则。 *)

(** ** Unit and Binary Operations with Only the Needed Choices

    Fix native Applicatives at that bound. Lifted Yoneda gives their Day
    units without convolution choices. Binary extension needs just the
    indicated self-convolution; preservation needs the two endpoint choices. *)

(** ** 只使用所需选择的单位与二元运算

    固定此界处的原生 Applicative。提升 Yoneda 无须卷积选择即给出其 Day 单位。
    二元延拓只需指定自身卷积；保持性只需两个端点选择。 *)

Section Operations.
Universe u.
Let SC
  : Cat
  := SetCat@{u u _ _ _ _ _}.
Let SM
  : HasMonoidal SC
  := SetCartMonoidal.

(** Extend the exact inherited lax unit, keeping the same functor. *)

(** 延拓相同的继承 lax 单位，保持同一函子。 *)

Definition ApplicativeDayUnitN
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : DayUnitF UnitS@{u u} ⇒ A
  := DayUnitExtendN UnitS A (lax_unit A tt).

(** A constant representable arrow recovers the original pure value. *)

(** 常值可表箭头恢复原纯值。 *)

Lemma applicative_day_unit_pure
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    (X : SetC@{u u}) (x : X)
  : ApplicativeDayUnitN A X {|lower := const_resp UnitS x|} ≈S pure[A] X x.
Proof.
  symmetry. exact (set_applicative_pure_roundtrip A X x).
Defined.

(** Extend the original tensorator, requiring only this convolution. *)

(** 延拓原张量子，只要求此卷积。 *)

Definition ApplicativeDayMulN
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    `{HA : !HasDay SC (tensorF (isMagmoidal SM)) A A}
  : DayF (tensorF (isMagmoidal SM)) A A ⇒ A
  := DayExtendN (tensorF (isMagmoidal SM)) (LaxDayTensorN SM A).

(** A weighted generator computes to the existing binary lifting. *)

(** 加权生成元计算为已有二元提升。 *)

Lemma applicative_day_mul_inject
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    `{HA : !HasDay SC (tensorF (isMagmoidal SM)) A A}
    {X Y Z : SetC@{u u}} (h : X ×S Y →r Z)
  : ApplicativeDayMulN A Z ∘ day_inject (tensorF (isMagmoidal SM)) A A (X,Y) h ≈
      lift₂[A; h].
Proof.
  exact (day_extend_β (tensorF (isMagmoidal SM))
    (LaxDayTensorN SM A) (X,Y) h).
Defined.

(** Day unit preservation is exactly preservation of all pure values.
    This uses singleton uniqueness, without any convolution choices. *)

(** Day 单位保持性恰为全部纯值保持性；这里使用单元素唯一性，不需卷积选择。 *)

Lemma applicative_day_unit_hom
    (A B : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    (α : A ⇒ B)
  : ((α ∘Nv ApplicativeDayUnitN A) ≈N ApplicativeDayUnitN B) ↔
      (∀ X, α X ∘ pure[A] X ≈ pure[B] X).
Proof.
  pose proof (day_unit_hom_law UnitS A B
    (ApplicativeDayUnitN A) (ApplicativeDayUnitN B) α) as H.
  split.
  - intros E X x.
    change (α X (pure[A] X x) ≈S pure[B] X x).
    rewrite <- (applicative_day_unit_pure A X x),
      <- (applicative_day_unit_pure B X x).
    exact (E X {|lower := const_resp UnitS x|}).
  - intros E. apply (snd H).
    transitivity (α UnitS (lax_unit A tt)).
    + apply (@func_proper _ _ (α UnitS)).
      exact (day_unit_value_extend UnitS A (lax_unit A tt)).
    + transitivity (lax_unit B tt).
      * transitivity (α UnitS (pure[A] UnitS tt)).
        -- apply (@func_proper _ _ (α UnitS)). symmetry.
           exact (applicative_pure_unit A tt).
        -- transitivity (pure[B] UnitS tt).
           ++ exact (E UnitS tt).
           ++ exact (applicative_pure_unit B tt).
      * symmetry. exact (day_unit_value_extend UnitS B (lax_unit B tt)).
Defined.

(** Day multiplication preservation is exactly preservation of the original
    ordered pairing, by the existing inverse universal correspondence. *)

(** 由已有互逆泛对应，Day 乘法保持性恰为原有序配对保持性。 *)

Lemma applicative_day_mul_hom
    (A B : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    `{HA : !HasDay SC (tensorF (isMagmoidal SM)) A A}
    `{HB : !HasDay SC (tensorF (isMagmoidal SM)) B B} (α : A ⇒ B)
  : ((α ∘Nv ApplicativeDayMulN A) ≈N
      (ApplicativeDayMulN B ∘Nv
        @DayMapN SC (tensorF (isMagmoidal SM)) A B A B HA HB α α)) ↔
      (∀ X Y, α (X ×S Y) ∘ φ₂[A; X; Y] ≈
        φ₂[B; X; Y] ∘ (α X × α Y)).
Proof.
  pose proof (day_mul_hom_law (tensorF (isMagmoidal SM)) A B
    (ApplicativeDayMulN A) (ApplicativeDayMulN B) α) as H.
  split.
  - intros E X Y [x y].
    pose proof (fst H E X Y x y) as K.
    transitivity (α (X ×S Y)
      (DayRestrictN (tensorF (isMagmoidal SM)) (ApplicativeDayMulN A) (X,Y) (x,y))).
    + apply (@func_proper _ _ (α (X ×S Y))). symmetry.
      exact (day_restrict_extend (tensorF (isMagmoidal SM))
        (LaxDayTensorN SM A) (X,Y) (x,y)).
    + transitivity (DayRestrictN (tensorF (isMagmoidal SM)) (ApplicativeDayMulN B)
        (X,Y) (α X x,α Y y)).
      * exact K.
      * exact (day_restrict_extend (tensorF (isMagmoidal SM)) (LaxDayTensorN SM B)
          (X,Y) (α X x,α Y y)).
  - intros E. apply (snd H). intros X Y x y.
    transitivity (α (X ×S Y) (φ₂[A; X; Y] (x,y))).
    + apply (@func_proper _ _ (α (X ×S Y))).
      exact (day_restrict_extend (tensorF (isMagmoidal SM))
        (LaxDayTensorN SM A) (X,Y) (x,y)).
    + transitivity (φ₂[B; X; Y] (α X x,α Y y)).
      * exact (E X Y (x,y)).
      * symmetry.
        exact (day_restrict_extend (tensorF (isMagmoidal SM)) (LaxDayTensorN SM B)
          (X,Y) (α X x,α Y y)).
Defined.

End Operations.

(** ** Structures and Operation-Preserving Round Trips

    Supply uniform Day choices on the common-bound native category. Reuse
    the accepted monoid/lax correspondence and canonical native pure; do
    not prove new monoid or Applicative structure laws. Existence is an
    explicit conditional input, not a construction of these uniform choices. *)

(** ** 结构与保持运算的往返

    在共同界原生范畴上提供统一 Day 选择。复用已验收的幺半群／lax 对应及规范
    原生纯值，不重证幺半群或 Applicative 结构律。存在性是显式条件输入，
    不在此构造这些统一选择。 *)

Section Structures.
Universe u.
Let SC
  : Cat
  := SetCat@{u u _ _ _ _ _}.
Let SM
  : HasMonoidal SC
  := SetCartMonoidal.
Context `(HD : ∀ F G : Fct SC SC, HasDay SC (tensorF (isMagmoidal SM)) F G).
Let DM
  : HasMonoidal (FctCat SC SC)
  := MonoidalDay SM HD.

(** Use the exact inherited lax structure as a Day monoid. *)

(** 将相同继承的 lax 结构用作 Day 幺半群。 *)

Definition ApplicativeDayMonoid
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : MonoidObj DM
  := LaxDayMonoid SM HD A.

(** Restrict a Day monoid and recover its canonical native pure values. *)

(** 限制 Day 幺半群，并恢复其规范原生纯值。 *)

Definition DayMonoidA (M : MonoidObj DM)
  : Applicative SC SetCat_HasTerminal SetCat_HasProduct
  := SetLaxA (DayMonoidLax SM HD M).

(** The supplied natural transformation preserves direct operations exactly
    when it preserves both Day monoid operations. *)

(** 所给自然变换保持直接运算，当且仅当保持两项 Day 幺半群运算。 *)

Theorem applicative_day_monoid_hom
    (A B : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    (α : A ⇒ B)
  : is_applicative_hom A B α ↔
      is_monoid_hom (ApplicativeDayMonoid A) (ApplicativeDayMonoid B) α.
Proof.
  split; intros H.
  - apply (fst (lax_day_monoid_hom SM HD A B α)).
    exact (fst (set_applicative_hom_lax A B α) H).
  - apply (snd (set_applicative_hom_lax A B α)).
    exact (snd (lax_day_monoid_hom SM HD A B α) H).
Defined.

(** Conversely, a Day homomorphism is exactly an Applicative comparison
    on the same underlying natural transformation. *)

(** 反之，Day 同态恰为同一底层自然变换上的 Applicative 比较。 *)

Theorem day_monoid_applicative_hom (M N : MonoidObj DM)
    (α : MonoidCarrier M ⇒ MonoidCarrier N)
  : is_monoid_hom M N α ↔ is_applicative_hom (DayMonoidA M) (DayMonoidA N) α.
Proof.
  split; intros H.
  - apply (snd (set_lax_applicative_hom
      (DayMonoidLax SM HD M) (DayMonoidLax SM HD N) α)).
    exact (fst (day_monoid_hom_laws SM HD M N α) H).
  - apply (snd (day_monoid_hom_laws SM HD M N α)).
    exact (fst (set_lax_applicative_hom
      (DayMonoidLax SM HD M) (DayMonoidLax SM HD N) α) H).
Defined.

(** Pure survives extension and restriction by singleton uniqueness and
    the existing lax unit round trip. *)

(** 由单元素唯一性及已有 lax 单位往返，纯值在延拓后限制中保持不变。 *)

Lemma day_applicative_pure_roundtrip
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : pure[DayMonoidA (ApplicativeDayMonoid A)] ≈N pure[A].
Proof.
  symmetry. apply (set_pure_unique A
    (lax_unit (DayMonoidLax SM HD (ApplicativeDayMonoid A)) tt) (pure[A])).
  transitivity (lax_unit A tt).
  - exact (applicative_pure_unit A tt).
  - symmetry. exact (day_lax_unit_roundtrip SM HD A tt).
Defined.

(** Pairing reuses the already proved tensorator round trip. *)

(** 配对复用已经证明的张量子往返。 *)

Lemma day_applicative_tensor_roundtrip
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : lax_tensorN (DayMonoidA (ApplicativeDayMonoid A)) ≈N lax_tensorN A.
Proof. exact (day_lax_tensor_roundtrip SM HD A). Defined.

(** Every binary lifting is preserved, without expanding selected coends. *)

(** 每个二元提升都保持不变，无须展开选定 coend。 *)

Lemma day_applicative_lift2_roundtrip
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    {X Y Z : SetC@{u u}} (h : X ×S Y →r Z)
  : lift₂[DayMonoidA (ApplicativeDayMonoid A); h] ≈ lift₂[A; h].
Proof.
  unfold lax_lift2. apply comp_proper; [reflexivity|].
  exact (day_applicative_tensor_roundtrip A (X,Y)).
Defined.

(** In the explicitly selected native closed model, application is the
    same lifted evaluation in both presentations. *)

(** 在显式选定的原生闭模型中，两种呈现的应用是同一个提升求值。 *)

Lemma day_applicative_ap_roundtrip
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    (X Y : SetC@{u u})
  : @applicative_ap SC SetCat_HasTerminal SetCat_HasProduct
      SetCat_HasExponential (DayMonoidA (ApplicativeDayMonoid A)) X Y ≈
    @applicative_ap SC SetCat_HasTerminal SetCat_HasProduct
      SetCat_HasExponential A X Y.
Proof. exact (day_applicative_lift2_roundtrip A eval_resp). Defined.

(** The identity comparison preserves recovered pure and pairing. *)

(** 恒等比较保持恢复所得纯值和配对。 *)

Lemma day_applicative_roundtrip_hom
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : is_applicative_hom (DayMonoidA (ApplicativeDayMonoid A)) A IdN.
Proof.
  split.
  - intros X x. exact (day_applicative_pure_roundtrip A X x).
  - intros X Y [x y]. exact (day_applicative_tensor_roundtrip A (X,Y) (x,y)).
Defined.

(** Its chosen inverse reuses general Applicative inverse preservation. *)

(** 其选定逆复用一般 Applicative 逆保持性。 *)

Lemma day_applicative_roundtrip_inv_hom
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : is_applicative_hom A (DayMonoidA (ApplicativeDayMonoid A)) IdN.
Proof.
  exact (applicative_hom_inverse (DayMonoidA (ApplicativeDayMonoid A)) A IdN
    (day_applicative_roundtrip_hom A) (nat_id_iso A)).
Defined.

(** The original Day unit is recovered by the accepted monoid round trip. *)

(** 原 Day 单位由已验收的幺半群往返恢复。 *)

Lemma applicative_day_unit_roundtrip (M : MonoidObj DM)
  : monoid_object_unit (ApplicativeDayMonoid (DayMonoidA M)) ≈N
      monoid_object_unit M.
Proof. exact (day_monoid_unit_roundtrip SM HD M). Defined.

(** The original Day multiplication is recovered by the same round trip. *)

(** 原 Day 乘法由同一往返恢复。 *)

Lemma applicative_day_mul_roundtrip (M : MonoidObj DM)
  : monoid_object_mul (ApplicativeDayMonoid (DayMonoidA M)) ≈N
      monoid_object_mul M.
Proof. exact (day_monoid_mul_roundtrip SM HD M). Defined.

(** Reuse the existing operation-preserving Day identity comparison. *)

(** 复用已有保持运算的 Day 恒等比较。 *)

Lemma applicative_day_roundtrip_hom (M : MonoidObj DM)
  : is_monoid_hom (ApplicativeDayMonoid (DayMonoidA M)) M IdN.
Proof. exact (day_monoid_roundtrip_hom SM HD M). Defined.

(** The reverse identity also reuses its existing preservation witness. *)

(** 反向恒等也复用已有保持性见证。 *)

Lemma applicative_day_roundtrip_inv_hom (M : MonoidObj DM)
  : is_monoid_hom M (ApplicativeDayMonoid (DayMonoidA M)) IdN.
Proof. exact (day_monoid_roundtrip_inv_hom SM HD M). Defined.

End Structures.
