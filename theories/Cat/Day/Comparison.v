From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Terminal
  Cat.Monoidal.Cartesian.
From Cats Require Export
  Cat.Day.Morphism.

(** * The Day Monoid and Lax Functor Equivalence *)

(** * Day 幺半群与 Lax 函子的等价 *)

(** ** Functors on Operation-Preserving Transformations

    Fix a monoidal base and explicit uniform Day choices. Both existing
    object conversions keep their underlying functor. Transfer the two
    preservation predicates to act on the same natural transformations. *)

(** ** 保持运算的变换上的函子

    固定幺半基及显式统一 Day 选择。已有两个对象转换均保持底层函子；运输
    两个保持性谓词，在同一自然变换上定义作用。 *)

Section Comparison.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C)
    (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}),
      HasDay C (tensorF MC) F G).
Local Existing Instance HD.
Let DM
  : MonoidalCat (FctCat C (SetCat@{u p _ _ _ _ _}))
  := MonoidalDay MC HD.
Let SM
  : MonoidalCat (SetCat@{u p _ _ _ _ _})
  := @CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct.

(** Extend lax functors and their monoidal transformations to Day monoids. *)

(** 将 lax 函子及其幺半变换延拓为 Day 幺半群。 *)

Program Definition LaxDayMonoidF
  : Fct (LaxMonoidalFctCat MC SM) (MonoidCat DM)
  :=
  {|F0 := LaxDayMonoid MC HD
  ; F1 L K α := (α.1; fst (lax_day_monoid_hom MC HD L K α.1) α.2)
  |}.
Next Obligation. intros α β E. exact E. Defined.
Next Obligation. intros Q x. reflexivity. Defined.
Next Obligation. intros Q x. reflexivity. Defined.

(** Restrict Day monoids and homomorphisms to the native lax presentation. *)

(** 将 Day 幺半群及同态限制为原生 lax 呈现。 *)

Program Definition DayMonoidLaxF
  : Fct (MonoidCat DM) (LaxMonoidalFctCat MC SM)
  :=
  {|F0 := DayMonoidLax MC HD
  ; F1 M N α := (α.1; fst (day_monoid_hom_laws MC HD M N α.1) α.2)
  |}.
Next Obligation. intros α β E. exact E. Defined.
Next Obligation. intros Q x. reflexivity. Defined.
Next Obligation. intros Q x. reflexivity. Defined.

(** ** Identity Components Preserve the Recovered Operations

    Retain those choices and reuse the proved unit/multiplication round
    trips. Identity components are homomorphisms between the two structures;
    this does not identify either the structures or their law witnesses. *)

(** ** 恒等分量保持恢复所得运算

    保持上述选择并复用已证明的单位／乘法往返。恒等分量是两结构之间的同态，
    不识别结构或其定律见证。 *)

(** The lax round-trip comparison preserves unit and tensorator. *)

(** Lax 往返比较保持单位与张量子。 *)

Lemma day_lax_roundtrip_hom (L : LaxMonoidalFct MC SM)
  : is_lax_monoidal_hom (DayMonoidLax MC HD (LaxDayMonoid MC HD L)) L idN.
Proof.
  split.
  - intros []. exact (day_lax_unit_roundtrip MC HD L tt).
  - intros X Y [x y]. exact (day_lax_tensor_roundtrip MC HD L (X,Y) (x,y)).
Defined.

(** Use the general chosen-inverse preservation theorem for its inverse. *)

(** 对其逆复用一般的指定逆保持性定理。 *)

Lemma day_lax_roundtrip_inv_hom (L : LaxMonoidalFct MC SM)
  : is_lax_monoidal_hom L (DayMonoidLax MC HD (LaxDayMonoid MC HD L)) idN.
Proof.
  exact (lax_monoidal_hom_inverse
    (DayMonoidLax MC HD (LaxDayMonoid MC HD L)) L idN
    (day_lax_roundtrip_hom L)
    (nt_id_NatIso L)).
Defined.

(** The Day round trip preserves both operations in designated equality. *)

(** Day 往返按指定相等保持两项运算。 *)

Lemma day_monoid_roundtrip_hom (M : MonoidObj DM)
  : is_monoid_hom (LaxDayMonoid MC HD (DayMonoidLax MC HD M)) M idN.
Proof.
  split.
  - intros X x. exact (day_monoid_unit_roundtrip MC HD M X x).
  - change (monoid_object_mul
      (LaxDayMonoid MC HD (DayMonoidLax MC HD M)) ≈N
      (monoid_object_mul M ∘Nv @tensor_map _ DM _ _ _ _ idN idN)).
    rewrite (@tensor_map_id _ DM (MonoidCarrier M) (MonoidCarrier M)).
    intros X x. exact (day_monoid_mul_roundtrip MC HD M X x).
Defined.

(** The reverse identity component uses the same round-trip equations. *)

(** 反向恒等分量使用相同的往返方程。 *)

Lemma day_monoid_roundtrip_inv_hom (M : MonoidObj DM)
  : is_monoid_hom M (LaxDayMonoid MC HD (DayMonoidLax MC HD M)) idN.
Proof.
  split.
  - intros X x. symmetry. exact (day_monoid_unit_roundtrip MC HD M X x).
  - change (monoid_object_mul M ≈N
      (monoid_object_mul (LaxDayMonoid MC HD (DayMonoidLax MC HD M)) ∘Nv
        @tensor_map _ DM _ _ _ _ idN idN)).
    rewrite (@tensor_map_id _ DM
      (MonoidCarrier (LaxDayMonoid MC HD (DayMonoidLax MC HD M)))
      (MonoidCarrier (LaxDayMonoid MC HD (DayMonoidLax MC HD M)))).
    intros X x. symmetry. exact (day_monoid_mul_roundtrip MC HD M X x).
Defined.

(** ** Natural Round Trips and Category Equivalence

    At both presentations identity components commute with every underlying
    transformation. Store the chosen comparisons and their transparent
    inverses, then package the ordinary equivalence in [CatCat]. *)

(** ** 自然往返与范畴等价

    在两种呈现中，恒等分量均与所有底层变换交换。保存选定比较及其透明逆，
    再将通常范畴等价打包在 [CatCat] 中。 *)

(** The lax round trip is naturally compared with identity. *)

(** Lax 往返与恒等之间具有自然比较。 *)

Program Definition DayLaxRoundtripN
  : (DayMonoidLaxF ∘F LaxDayMonoidF) ⇒ (@IdF (LaxMonoidalFctCat MC SM))
  :=
  {|nt L := (idN; day_lax_roundtrip_hom L)
  |}.
Next Obligation. intros Q x. reflexivity. Defined.

(** Its reverse comparison keeps the same identity components. *)

(** 其反向比较保持相同恒等分量。 *)

Program Definition DayLaxRoundtripInvN
  : (@IdF (LaxMonoidalFctCat MC SM)) ⇒ (DayMonoidLaxF ∘F LaxDayMonoidF)
  :=
  {|nt L := (idN; day_lax_roundtrip_inv_hom L)
  |}.
Next Obligation. intros Q x. reflexivity. Defined.

(** Both chosen comparisons are inverse by the underlying identity laws. *)

(** 由底层恒等律，两个选定比较互逆。 *)

Definition day_lax_roundtrip_iso
  : (DayMonoidLaxF ∘F LaxDayMonoidF) ≅N (@IdF (LaxMonoidalFctCat MC SM)).
Proof.
  exists DayLaxRoundtripN. intros L.
  exists (DayLaxRoundtripInvN L). split; intros X x; reflexivity.
Defined.

(** The Day monoid round trip is naturally compared with identity. *)

(** Day 幺半群往返与恒等之间具有自然比较。 *)

Program Definition DayMonoidRoundtripN
  : (LaxDayMonoidF ∘F DayMonoidLaxF) ⇒ (@IdF (MonoidCat DM))
  :=
  {|nt M := _
  |}.
Next Obligation.
  refine (idN; _). split.
  - intros Q x. exact (day_monoid_unit_roundtrip MC HD M Q x).
  - change (monoid_object_mul
      (LaxDayMonoid MC HD (DayMonoidLax MC HD M)) ≈N
      (monoid_object_mul M ∘Nv @tensor_map _ DM _ _ _ _ idN idN)).
    rewrite (@tensor_map_id _ DM (MonoidCarrier M) (MonoidCarrier M)).
    intros Q x. exact (day_monoid_mul_roundtrip MC HD M Q x).
Defined.
Next Obligation. intros Q x. reflexivity. Defined.

(** The reverse comparison preserves the same chosen Day operations. *)

(** 反向比较保持相同选定 Day 运算。 *)

Program Definition DayMonoidRoundtripInvN
  : (@IdF (MonoidCat DM)) ⇒ (LaxDayMonoidF ∘F DayMonoidLaxF)
  :=
  {|nt M := _
  |}.
Next Obligation.
  refine (idN; _). split.
  - intros Q x. symmetry. exact (day_monoid_unit_roundtrip MC HD M Q x).
  - change (monoid_object_mul M ≈N
      (monoid_object_mul (LaxDayMonoid MC HD (DayMonoidLax MC HD M)) ∘Nv
        @tensor_map _ DM _ _ _ _ idN idN)).
    rewrite (@tensor_map_id _ DM
      (MonoidCarrier (LaxDayMonoid MC HD (DayMonoidLax MC HD M)))
      (MonoidCarrier (LaxDayMonoid MC HD (DayMonoidLax MC HD M)))).
    intros Q x. symmetry. exact (day_monoid_mul_roundtrip MC HD M Q x).
Defined.
Next Obligation. intros Q x. reflexivity. Defined.

(** The Day monoid comparison is a natural isomorphism, not record equality. *)

(** Day 幺半群比较是自然同构，不是记录相等。 *)

Definition day_monoid_roundtrip_iso
  : (LaxDayMonoidF ∘F DayMonoidLaxF) ≅N (@IdF (MonoidCat DM)).
Proof.
  exists DayMonoidRoundtripN. intros M.
  exists (DayMonoidRoundtripInvN M). split; intros X x; reflexivity.
Defined.

(** Lax monoidal setoid-valued functors are equivalent to Day monoids on
    objects and monoidal transformations, under the stated Day choices. *)

(** 在所述 Day 选择下，广集值 lax 幺半函子与 Day 幺半群在对象及幺半变换上
    范畴等价。 *)

Definition day_lax_monoid_equiv
  : LaxMonoidalFctCat MC SM ≃C MonoidCat DM
  := (LaxDayMonoidF; (DayMonoidLaxF;
      (day_lax_roundtrip_iso,day_monoid_roundtrip_iso))).

(** The chosen unit and counit satisfy the forward comparison triangle. *)

(** 选定单位与余单位满足正向比较三角形。 *)

Lemma day_comparison_triangle_lax (L : LaxMonoidalFct MC SM)
  : DayMonoidRoundtripN (LaxDayMonoidF L) ∘
      fmap LaxDayMonoidF (DayLaxRoundtripInvN L) ≈ id.
Proof. intros X x. change (x ≈S x). reflexivity. Defined.

(** The reverse triangle likewise compares only underlying transformations. *)

(** 反向三角形同样只比较底层变换。 *)

Lemma day_comparison_triangle_monoid (M : MonoidObj DM)
  : fmap DayMonoidLaxF (DayMonoidRoundtripN M) ∘
      DayLaxRoundtripInvN (DayMonoidLaxF M) ≈ id.
Proof. intros X x. change (x ≈S x). reflexivity. Defined.

End Comparison.
