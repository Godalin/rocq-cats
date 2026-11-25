From Cats Require Import
  Cat.Gluing.Fibration
  Cat.Pullback
  Instance.Set.Core
  Instance.Set.Pullback
  Instance.Bool.Action.
From CatsGluingTests Require Import
  Gluing.

(** * Gluing Fibration Interfaces and Computation

    Keep independent category sizes, explicit choice and observable
    equality witnesses. A nonidentity boolean action also tests a genuine
    change of base; the gluing functor need not preserve chosen pullbacks. *)

(** * 粘合纤维化的接口及计算

    保持范畴大小独立、选择显式及相等见证可观测。非恒等布尔作用还检验真正
    的基变换；粘合函子不必保持选定拉回。 *)

(** ** Independent Source and Target Levels

    Source equality is above its hom carrier, target equality below it.
    Object and auxiliary law levels remain separate across the categories. *)

(** ** 独立的源与目标层级

    源相等位于其 Hom 载体之上，目标相等位于其载体之下。两个范畴的对象界
    与辅助律界亦保持分离。 *)

Section IndependentLevels.
Universes oc hc ec lc od hd ed ld.
Constraint hc < ec, ec < oc, oc < lc.
Constraint ed < hd, hd < od, od < ld.
Constraint lc < od.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F : Fct C D).

(** No chosen structures occur in the candidate equivalence. *)

(** 候选等价不出现选定结构。 *)

Definition independent_gluing_cartesian {X Y : Gluing F} (f : Hom X Y)
  : f ⦂ Cart(GluingRightF F) ↔
    is_pullback (fmap F (comma_right f)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left f)
  := gluing_cartesian_iff_pullback F f.

(** Just the required pullback family supplies the chosen lifts. *)

(** 仅所需的拉回族即可提供选定提升。 *)

Definition independent_gluing_lifts
    (pullbacks : ∀ (Y : Gluing F) (A : C)
      (σ : Hom A (comma_right_ob Y)),
      ∃ R : D, ∃ r : Hom R (F A), ∃ v : Hom R (comma_left_ob Y),
        is_pullback (fmap F σ) (comma_arrow Y) R r v)
  : HasCartLift (GluingRightF F)
  := GluingRightF_HasCartLift F pullbacks.

End IndependentLevels.

(** ** Reversed Independent Levels

    Reverse both hom/equality orders and the source/target object and law
    orders. The convenience wrapper still preserves the native boundaries. *)

(** ** 反向的独立层级

    同时反转两端 Hom／相等次序及源／目标对象与律界次序；便捷包装仍保持
    原有边界。 *)

Section ReversedLevels.
Universes oc hc ec lc od hd ed ld.
Constraint ec < hc, hc < oc, oc < lc.
Constraint hd < ed, ed < od, od < ld.
Constraint ld < oc.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F : Fct C D) `{HP : !HasPullback D}.

(** The candidate equivalence also accepts the reversed profile. *)

(** 候选等价也接受反向配置。 *)

Definition reversed_gluing_cartesian {X Y : Gluing F} (f : Hom X Y)
  : f ⦂ Cart(GluingRightF F) ↔
    is_pullback (fmap F (comma_right f)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left f)
  := gluing_cartesian_iff_pullback F f.

(** Importing the wrapper must not select lifts automatically. *)

(** 导入此包装不应自动选择提升。 *)

Fail Definition unchosen_gluing_lifts
  : HasCartLift (GluingRightF F)
  := ltac:(typeclasses eauto).

(** Explicit selection reuses all-target pullbacks only when requested. *)

(** 只有显式要求时才复用目标全部拉回。 *)

Definition reversed_gluing_lifts
  : HasCartLift (GluingRightF F)
  := GluingRightF_PullbackHasCartLift F.

End ReversedLevels.

(** ** Setoid Factors over an Ignored Tag

    Enable the original setoid pullbacks locally. Equivalent maps can
    change tags and equality witnesses; cartesian factorization compares
    their values rather than their stored proofs. *)

(** ** 忽略标签的广集上的分解

    局部启用原有广集拉回。等价映射可改变标签及相等见证；笛卡尔分解比较
    其值而非保存的证明。 *)

Section SetoidFactors.
Local Instance set_pullbacks
  : HasPullback SetCat
  := SetCat_HasPullback.

(** The lifted object is the original setoid pullback over a tag toggle. *)

(** 提升对象是沿标签翻转得到的原广集拉回。 *)

Definition TaggedReindexedOb
  : Gluing (@IdF SetCat)
  := GluingPullbackOb IdF (Pb gluing_toggle id) (pb1 _ _).

(** Keep the requested base map exactly, and the second projection on top. *)

(** 原样保留给定基映射，并以第二投影作为顶边。 *)

Definition tagged_reindex_lift
  : (@Hom (Gluing (@IdF SetCat))) TaggedReindexedOb TaggedGluingObj
  := gluing_pullback_lift IdF TaggedGluingObj gluing_toggle
      (Pb gluing_toggle id) (pb1 _ _) (pb2 _ _) pullback_universal.

(** The candidate cartesian witness needs only this one pullback. *)

(** 候选笛卡尔见证只需要这一个拉回。 *)

Definition tagged_reindex_cartesian
  : tagged_reindex_lift ⦂ Cart(GluingRightF (@IdF SetCat))
  := gluing_pullback_lift_cartesian IdF TaggedGluingObj gluing_toggle
      (Pb gluing_toggle id) (pb1 _ _) (pb2 _ _) pullback_universal.

(** Use the generic cartesian factor; the implementation extracts the
    existing arrow-category mediator. *)

(** 使用一般笛卡尔分解；实现提取原有箭头范畴中介。 *)

Definition tagged_factor
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedReindexedOb
  := cartesian_factor tagged_reindex_cartesian tagged_gluing_toggle id
      (comp_resp_id_r gluing_toggle).

(** Its top map computes both pullback coordinates. *)

(** 其顶边计算拉回的两个坐标。 *)

Example tagged_factor_values_compute
  : ((comma_left tagged_factor (3, false)).1,
      (comma_left tagged_factor (3, false)).2.1) =
      ((3, false), (3, true)).
Proof. reflexivity. Defined.

(** The supplied base factor remains the original identity function. *)

(** 给定基分解仍为原恒等函数。 *)

Example tagged_factor_base_computes
  : comma_right tagged_factor (3, false) = (3, false).
Proof. reflexivity. Defined.

(** A second factor uses a specified-equal square with different tag data. *)

(** 第二个分解使用指定相等、但标签数据不同的方形。 *)

Definition tagged_identity_factor
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedReindexedOb
  := cartesian_factor tagged_reindex_cartesian id id
      (λ x, (eq_refl, true)).

(** Reuse generic factor respectfulness, including commutativity-witness
    independence; native equality of these square records is unnecessary. *)

(** 复用一般分解保相等性，包括交换性见证独立性；不需要这些方形记录原生相等。 *)

Example tagged_factor_respects
  : tagged_factor ≈ tagged_identity_factor.
Proof.
  apply cartesian_factor_proper; [exact tagged_gluing_toggle_equal | reflexivity].
Defined.

(** Recover a target mediator through the reverse candidate theorem.
    Its cone has the identity and the tag toggle as projections. *)

(** 通过反向候选定理恢复目标中介；输入锥以恒等及标签翻转作为投影。 *)

Definition recovered_tagged_mediator
  : TaggedGluingS →r comma_left_ob TaggedReindexedOb
  := (snd (gluing_cartesian_pullback IdF tagged_reindex_lift
      tagged_reindex_cartesian) TaggedGluingS id gluing_toggle
      (λ x, (eq_refl, true))).1.

(** The reverse theorem retains the same transparent coordinate computation. *)

(** 反向定理保留同样透明的坐标计算。 *)

Example recovered_tagged_mediator_computes
  : ((recovered_tagged_mediator (3, false)).1,
      (recovered_tagged_mediator (3, false)).2.1) =
      ((3, false), (3, true)).
Proof. reflexivity. Defined.

(** Membership keeps an observable token. *)

(** 隶属关系保留可观测标记。 *)

Definition tagged_pullback_token
  : comma_left_ob TaggedReindexedOb
  := ((3, false); ((3, true); (eq_refl, true))).

(** The pullback witness is computational data, not a truncated assertion. *)

(** 拉回见证为计算数据，并非截断断言。 *)

Example tagged_pullback_token_computes
  : snd tagged_pullback_token.2.2 = true.
Proof. reflexivity. Defined.

End SetoidFactors.

(** ** A Nonidentity Semantic Action

    The nonidentity loop acts by negation. Its lifted arrow keeps that loop
    as base, and factorization computes a pair with opposite booleans. *)

(** ** 非恒等语义作用

    非恒等环路以取反作用。提升箭头保留此环路作为基边；分解计算出两个布尔
    值相反的配对。 *)

Section BooleanAction.
Local Instance action_pullbacks
  : HasPullback SetCat
  := SetCat_HasPullback.

(** The semantic object is the identity arrow over the action's object. *)

(** 语义对象为作用对象上的恒等箭头。 *)

Program Definition ActionGluingOb
  : Gluing BoolActionF
  :=
  {|comma_left_ob := BoolActionF tt
  ; comma_right_ob := tt
  ; comma_arrow := id
  |}.

(** Its nontrivial square has the semantic action as top side. *)

(** 其非平凡方形以语义作用作为顶边。 *)

Program Definition action_square
  : (@Hom (Gluing BoolActionF)) ActionGluingOb ActionGluingOb
  :=
  {|comma_left := fmap BoolActionF bool_loop
  ; comma_right := bool_loop
  |}.
Next Obligation. intros b. reflexivity. Defined.

(** Select the available lift explicitly for this model. *)

(** 为此模型显式选择已有提升。 *)

Local Instance action_lifts
  : HasCartLift (GluingRightF BoolActionF)
  := GluingRightF_PullbackHasCartLift BoolActionF.

(** The chosen base remains the requested object by native computation. *)

(** 选定基对象经原生计算仍为所要求的对象。 *)

Example action_lift_base_computes
  : cartesian_lift_base (P := GluingRightF BoolActionF)
      (Y := ActionGluingOb) bool_loop = eq_refl.
Proof. reflexivity. Defined.

(** The selected lifting arrow keeps the nonidentity loop. *)

(** 选定提升箭头保留非恒等环路。 *)

Example action_lift_arrow_computes
  : comma_right (cartesian_lift (P := GluingRightF BoolActionF)
      (Y := ActionGluingOb) bool_loop) = true.
Proof. reflexivity. Defined.

(** Factor the action square over an identity base factor. *)

(** 在恒等基分解上分解作用方形。 *)

Definition action_factor
  : (@Hom (Gluing BoolActionF)) ActionGluingOb
      (@CartLift _ _ (GluingRightF BoolActionF) action_lifts
        ActionGluingOb tt bool_loop)
  := cartesian_factor (@cartesian_lift_universal _ _
      (GluingRightF BoolActionF) action_lifts ActionGluingOb tt bool_loop)
      action_square (@Cats.Cat.Core.id BoolGpd tt) (comp_id_r bool_loop).

(** The two pullback coordinates exhibit the nonidentity action. *)

(** 两个拉回坐标体现非恒等作用。 *)

Example action_factor_values_compute
  : ((comma_left action_factor false).1,
      (comma_left action_factor false).2.1) = (false, true).
Proof. reflexivity. Defined.

End BooleanAction.
