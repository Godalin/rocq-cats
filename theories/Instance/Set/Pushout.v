From Cats Require Import
  Cat.Core
  Cat.Pushout
  Cat.Colimit.Finite
  Instance.Set.Core
  Instance.Set.Coproduct
  Instance.Set.Coequalizer.

(** * Pushouts from Setoid Coproducts and Coequalizers *)

(** * 从广集余积及余等化子得到推出 *)

(** Use the general opposite product/equalizer construction. The chosen
    object keeps disjoint-sum representatives with generated equality. *)

(** 使用一般反积／等化子构造；选定对象保留不交和代表及生成相等。 *)

Definition SetCat_HasPushout@{u p +}
  : HasPushout (SetCat@{u p _ _ _ _ _})
  := @CoproductCoequalizerPushout SetCat
      SetCat_HasCoproduct SetCat_HasCoequalizer.
