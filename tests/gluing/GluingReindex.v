From Cats Require Import
  Cat.Gluing.Reindex
  Cat.Pullback
  Instance.Set.Core
  Instance.Set.Pullback
  Instance.Set.Terminal
  Instance.Bool.Action.
From CatsTests.gluing Require Import
  Gluing
  GluingFibration.

(** * Fixed-Base Gluing and Coherent Reindexing

    Check opposite strict size orders, specified-equal vertical squares,
    transparent comparison maps and base changes between different objects.
    Pullback choices are explicit and shared with the lifting construction. *)

(** * 固定基对象粘合及相干重索引

    检查相反严格大小次序、指定相等的竖直方形、透明比较映射及不同对象间的
    基变换。拉回选择显式给出，并与提升构造共享。 *)

(** ** Independent Category Boundaries

    Source equality is larger than source homs, target equality smaller.
    The target object and law bounds exceed the source bounds strictly. *)

(** ** 独立范畴边界

    源相等大于源 Hom，目标相等小于目标 Hom；目标对象及律界严格大于源界。 *)

Section IndependentLevels.
Universes oc hc ec lc od hd ed ld.
Constraint hc < ec, ec < oc, oc < lc, lc < od.
Constraint ed < hd, hd < od, od < ld.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F : Fct C D) `{HP : !HasPullback D}.

(** The existing slice interface uses the target law bound for its hom
    carrier, retaining the smaller native target equality bound. *)

(** 既有切片接口以目标律界打包 Hom 载体，保持较小的原生目标相等界。 *)

Definition independent_gluing_fiber (A : C)
  : Cat@{od ld ed ld ld}
  := GluingFiber F A.

(** Its inclusion does not identify the source and target categories. *)

(** 其包含不等同源与目标范畴。 *)

Definition independent_fiber_inclusion (A : C)
  : Fct (GluingFiber F A) (Gluing F)
  := GluingFiberInclusionF F A.

(** Reindexing uses only the target's chosen pullbacks. *)

(** 重索引只使用目标的选定拉回。 *)

Definition independent_fiber_reindex {A B : C} (f : Hom A B)
  : Fct (GluingFiber F B) (GluingFiber F A)
  := GluingFiberReindexF F f.

(** Identity reindexing has a natural isomorphism at these strict levels. *)

(** 在这些严格层级下，恒等重索引具有自然同构。 *)

Definition independent_fiber_unit (A : C)
  : (@IdF (GluingFiber F A)) ≅N GluingFiberReindexF F (id[A])
  := gluing_fiber_reindex_id_iso F A.

(** Composition includes the nondefinitional functor-law boundary. *)

(** 复合包含非定义相等的函子律边界。 *)

Definition independent_fiber_composite {A B E : C} (f : Hom B E)
    (g : Hom A B)
  : (GluingFiberReindexF F g ∘F GluingFiberReindexF F f)
      ≅N GluingFiberReindexF F (f ∘ g)
  := gluing_fiber_reindex_comp_iso F f g.

End IndependentLevels.

(** ** Reversed Category Boundaries

    Reverse both hom/equality and source/target object/law orders. Slice
    arrows retain their triangle witnesses. The existing category packages
    their carrier at the target law bound; the native target hom stays small. *)

(** ** 反向范畴边界

    同时反转 Hom／相等及源／目标对象与律界次序。切片箭头保留三角形见证，
    既有范畴以目标律界打包其载体；原目标 Hom 仍保持较小。 *)

Section ReversedLevels.
Universes oc hc ec lc od hd ed ld.
Constraint ec < hc, hc < oc, oc < lc.
Constraint hd < ed, ed < od, od < ld, ld < oc.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F : Fct C D) `{HP : !HasPullback D}.

(** The equality witness remains in the original target equality universe. *)

(** 相等见证仍位于原目标相等宇宙。 *)

Definition reversed_gluing_fiber (A : C)
  : Cat@{od ld ed ld ld}
  := GluingFiber F A.

(** Identity comparisons also accept the reversed profile. *)

(** 恒等比较也接受反向配置。 *)

Definition reversed_fiber_unit (A : C)
  : (@IdF (GluingFiber F A)) ≅N GluingFiberReindexF F (id[A])
  := gluing_fiber_reindex_id_iso F A.

(** Composite comparisons retain independent ambient boundaries. *)

(** 复合比较保留独立环境边界。 *)

Definition reversed_fiber_composite {A B E : C} (f : Hom B E)
    (g : Hom A B)
  : (GluingFiberReindexF F g ∘F GluingFiberReindexF F f)
      ≅N GluingFiberReindexF F (f ∘ g)
  := gluing_fiber_reindex_comp_iso F f g.

(** Importing reindexing still does not enable gluing lifts automatically. *)

(** 导入重索引仍不自动启用粘合提升。 *)

Fail Definition unchosen_reindex_lifts
  : HasCartLift (GluingRightF F)
  := ltac:(typeclasses eauto).

End ReversedLevels.

(** ** Vertical Maps with Specified Equality

    Use the original tagged setoid, whose equality forgets tags and keeps
    Boolean evidence. A base map specified-equal to identity need not be
    the native identity function. *)

(** ** 带指定相等的竖直映射

    使用原标签广集，其相等忽略标签并保留布尔证据。指定等于恒等的基映射
    不必是原生恒等函数。 *)

Section TaggedVertical.

(** Read the original gluing object in its fixed-base presentation. *)

(** 在固定基对象表示中读取原粘合对象。 *)

Definition TaggedFiberOb
  : GluingFiber (@IdF SetCat) TaggedGluingS
  := GluingFiberOb IdF TaggedGluingObj.

(** The tag-changing square has a specified identity base. *)

(** 改变标签的方形具有指定恒等基边。 *)

Definition tagged_vertical_slice
  : (@Hom (GluingFiber (@IdF SetCat) TaggedGluingS)) TaggedFiberOb TaggedFiberOb
  := gluing_fiber_vertical_map (@IdF SetCat) TaggedGluingS
      (R := TaggedFiberOb) (S := TaggedFiberOb) tagged_gluing_toggle
      (snd tagged_gluing_toggle_equal).

(** Recovering the slice map keeps the changed tag by computation. *)

(** 经计算，恢复的切片映射保留改变后的标签。 *)

Example tagged_vertical_slice_computes
  : slice_map tagged_vertical_slice (3, false) = (3, true).
Proof. reflexivity. Defined.

(** The square round trip uses specified equality on both side maps. *)

(** 方形往返在两边使用指定相等。 *)

Example tagged_vertical_square_roundtrip
  : @HomEq (Gluing (@IdF SetCat)) TaggedGluingObj TaggedGluingObj
      (fmap (GluingFiberInclusionF (@IdF SetCat) TaggedGluingS)
        tagged_vertical_slice) tagged_gluing_toggle
  := gluing_fiber_vertical_roundtrip (@IdF SetCat) TaggedGluingS
      (R := TaggedFiberOb) (S := TaggedFiberOb) tagged_gluing_toggle
      (snd tagged_gluing_toggle_equal).

(** Included slice-map equality is reflected rather than replaced by
    native function equality. *)

(** 包含反映切片映射相等，不将它替换为原生函数相等。 *)

Example tagged_vertical_is_identity
  : @HomEq (GluingFiber (@IdF SetCat) TaggedGluingS)
      TaggedFiberOb TaggedFiberOb tagged_vertical_slice id.
Proof.
  apply (gluing_fiber_inclusion_faithful (@IdF SetCat) TaggedGluingS).
  transitivity tagged_gluing_toggle.
  - exact tagged_vertical_square_roundtrip.
  - transitivity (id[TaggedGluingObj]);
      [exact tagged_gluing_toggle_equal |].
    symmetry.
    exact (fmap_id (IsFct :=
      isFct (GluingFiberInclusionF (@IdF SetCat) TaggedGluingS))
      (X := TaggedFiberOb)).
Defined.

End TaggedVertical.

(** ** Boolean Action Comparisons

    The nonidentity loop acts by negation. Unit and composition comparisons
    retain the original slice inverse/mediator computations, even though
    the abstract functor laws are only specified equalities. *)

(** ** 布尔作用的比较

    非恒等环路以取反作用。单位及复合比较保留原切片逆／中介计算，尽管抽象
    函子律只是指定相等。 *)

Section BooleanComparisons.
Local Instance boolean_pullbacks
  : HasPullback SetCat
  := SetCat_HasPullback.

(** Read the old nonidentity action's gluing object in its slice. *)

(** 在切片中读取原非恒等作用的粘合对象。 *)

Definition BooleanFiberOb
  : GluingFiber BoolActionF tt
  := GluingFiberOb BoolActionF ActionGluingOb.

(** The identity comparison stores both original Boolean coordinates. *)

(** 恒等比较保存两个原布尔坐标。 *)

Example boolean_unit_computes
  : let x := slice_map (GluingFiberReindexIdN BoolActionF tt BooleanFiberOb)
      false in (x.1, x.2.1) = (false, false).
Proof. reflexivity. Defined.

(** The explicitly stored unit inverse computes the original element. *)

(** 显式保存的单位逆计算出原元素。 *)

Example boolean_unit_inverse_computes
  : slice_map ((gluing_fiber_reindex_id_iso BoolActionF tt).2
      BooleanFiberOb).1 (false; (false; eq_refl)) = false.
Proof. reflexivity. Defined.

(** Two successive negations retain an intermediate value and witnesses. *)

(** 两次取反保留中间值及见证。 *)

Definition boolean_iterated_point
  : slice_dom (GluingFiberReindexF BoolActionF bool_loop
      (GluingFiberReindexF BoolActionF bool_loop BooleanFiberOb))
  := (false; ((true; (false; eq_refl)); eq_refl)).

(** The composition comparison flattens the two original projections. *)

(** 复合比较将两个原投影展平。 *)

Example boolean_composite_computes
  : let x := slice_map (GluingFiberReindexCompN BoolActionF
      bool_loop bool_loop BooleanFiberOb) boolean_iterated_point in
    (x.1, x.2.1) = (false, false).
Proof. reflexivity. Defined.

(** The corresponding cartesian lifting arrow keeps the nonidentity base. *)

(** 对应笛卡尔提升箭头保留非恒等基边。 *)

Example boolean_slice_lift_base_computes
  : comma_right (gluing_fiber_lift BoolActionF bool_loop BooleanFiberOb) = true.
Proof. reflexivity. Defined.

End BooleanComparisons.

(** ** A Change between Distinct Base Objects

    Reindex the identity over the unit setoid along a constant map from the
    tagged setoid. This checks dependent endpoints beyond endomorphisms. *)

(** ** 不同基对象间的变换

    沿来自标签广集的常值映射重索引单位广集上的恒等。由此检查自同态以外的
    依赖端点。 *)

Section DistinctBases.
Local Instance distinct_pullbacks
  : HasPullback SetCat
  := SetCat_HasPullback.

(** The base map has different source and target carriers. *)

(** 基映射的源与目标载体不同。 *)

Program Definition tagged_to_unit
  : TaggedGluingS →r UnitS
  :=
  {|func _ := tt
  |}.
Next Obligation. intros x y H. exact tt. Defined.

(** Use the original identity arrow in the unit slice. *)

(** 使用单位切片中的原恒等箭头。 *)

Program Definition UnitFiberOb
  : GluingFiber (@IdF SetCat) UnitS
  :=
  {|slice_dom := UnitS
  ; slice_arrow := id
  |}.

(** The reindexed structure arrow now has the tagged setoid as base. *)

(** 重索引后的结构箭头以标签广集为基对象。 *)

Example distinct_base_projection_computes
  : slice_arrow (GluingFiberReindexF IdF tagged_to_unit UnitFiberOb)
      ((3, false); (tt; tt)) = (3, false).
Proof. reflexivity. Defined.

(** Its cartesian lifting square retains the original map to unit. *)

(** 其笛卡尔提升方形保留原来的单位映射。 *)

Example distinct_base_lift_computes
  : comma_right (gluing_fiber_lift IdF tagged_to_unit UnitFiberOb) (3, false)
      = tt.
Proof. reflexivity. Defined.

End DistinctBases.
