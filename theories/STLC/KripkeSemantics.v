From Cats Require Export STLC.NormalPresheaf.
From Cats Require Import
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Terminal
  Instance.Set.Lift
  Instance.Set.Kripke.

(** * Semantic Values for Normalization

    Interpretation follows the simple type. At base types a value is a
    lifted neutral term; unit has its singleton value, products have pairs,
    and arrows use the general coherent Kripke functions. Every type has a
    presheaf of values, so changing context is already a respectful action
    with identity and composition laws.

    Recursive function construction needs a common internal bound large
    enough for values, pointwise relations and their stored coherence laws.
    [SemF] uses that explicit bound [s]. It does not identify [s] with the
    signature level [b], world hom equality [r], or auxiliary law bound [l].
    [RaisedSemF] then raises carrier and equality bounds independently.
    These are transparent wrappers, not downward resizing. The internal
    choice of a common bound is not a general theorem equating carrier and
    equality universes of arbitrary Kripke functions.

    The bounds include [b <= s], [r <= s], [b <= l] and [r <= l].
    No order between the semantic bound [s] and the world-law bound [l]
    is needed. External raising requires [s <= u] and [s <= p].

    This interpretation supplies values only. Reflection, reification and
    evaluation are additional constructions; no normalization theorem or
    directed reduction claim follows from this definition alone. *)

(** * 正规化所用的语义值

    解释沿简单类型递归。基类型的值是提升后的中性项；单位类型只有单元素值，
    积类型使用配对，箭头类型使用一般的相容 Kripke 函数。每个类型都有一个
    值预层，因此更换上下文本身就是保持单位律与复合律的保相等作用。

    递归构造函数需要足以容纳值、逐点关系及所保存相容律的共同内部界限。
    [SemF] 显式使用界限 [s]，不将其与签名层级 [b]、世界 Hom 相等 [r] 或
    定律辅助界限 [l] 合并。[RaisedSemF] 随后独立提升载体与相等界限。
    这些是透明包装，不向下重设大小。内部选择共同界限，并不是任意 Kripke
    函数的载体与相等宇宙必然相同的定理。

    大小界限包含 [b <= s]、[r <= s]、[b <= l] 与 [r <= l]，不要求语义
    界限 [s] 与世界定律界限 [l] 之间有顺序。对外提升要求 [s <= u] 与
    [s <= p]。

    此解释只提供值。反射、实化与求值是额外构造；仅由此定义不能推出正规化
    定理或任何有向归约结论。 *)

Local Existing Instance SetCat_HasProduct.

(** Type-recursive semantic presheaves. Arrow values reuse the generic
    function presheaf, including all its coherence witnesses. *)

(** 沿类型递归的语义预层。箭头值复用一般函数预层，包括它的全部相容性见证。 *)

Fixpoint SemF@{b r s l +} {B : Type@{b}} (A : Ty B)
  : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}
  := match A with
  | ty_base b => LiftF ∘F NePsh (ty_base b)
  | ty_unit => ConstF ((RenamingCat B)^op) (C := SetCat) UnitS
  | ty_prod A U => PointwiseProductF (SemF A) (SemF U)
  | ty_arr A U => (SemF U) ^K (SemF A)
  end.

(** Independently enlarge the externally visible carrier and relation
    bounds. A value still retains the internal representative through
    [lower], and equality retains the original witness in another wrapper. *)

(** 独立扩大对外可见的载体与关系界限。值通过 [lower] 保留内部代表，相等则在
    另一个包装中保留原见证。 *)

Definition RaisedSemF@{b r s l u p +} {B : Type@{b}} (A : Ty B)
  : Fct ((RenamingCat B)^op)
      SetCat@{u p _ _ _ _ _}
  := LiftF ∘F
      (SemF A : Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}).
