From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Closed
  Cat.CatCat
  Cat.CCC
  Cat.Natural
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Equivalence.CCC
  Instance.Set.Core
  Instance.Set.CCC
  Instance.Bool.Group.

(** Importing transport constructors must not select a concrete CCC model. *)

(** 导入运输构造器不得选定具体 CCC 模型。 *)

Fail Definition unchosen_transport_model
  : CCC SetCat
  := ltac:(typeclasses eauto).

(** The two categories retain opposite strict hom/equality size orderings,
    including in the transported choices and both bundled functors. *)

(** 两侧范畴保持相反的严格 Hom／相等大小排列，包括运输选择及双向打包函子。 *)

Section IndependentLevels.
Universes o h p l.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l})
    (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF)
    (HC : CCC C) (HD : CCC D).

Definition low_eq_transport
  : CCC D
  := QuasiInverseCCC F G u v HC.
Definition high_eq_transport
  : CCC C
  := QuasiInverseCCC G F v u HD.
Definition mixed_forward_ccc_functor
  : CCCFunctor HC low_eq_transport
  := QuasiInverseCCCF F G u v HC low_eq_transport.
Definition mixed_inverse_ccc_functor
  : CCCFunctor low_eq_transport HC
  := QuasiInverseCCCF G F v u low_eq_transport HC.
End IndependentLevels.

(** Transport to a different category presentation, using the existing
    double-opposite equivalence and setoid models. Operations must compute
    through the lifted evaluations and Type-valued universal witnesses. *)

(** 使用已有双重反范畴等价和广集模型运输到不同范畴呈现；运算必须穿过提升
    求值及 Type 值泛性质见证计算。 *)

Module TransportComputations.

Definition E
  : SetCat ≃C ((SetCat^op)^op)
  := iso_symm (op_involution SetCat).
Definition TransportedCCC
  := EquivalenceCCC E SetCat_CCC.
Local Existing Instance TransportedCCC.

Example transported_pair_computes
  : @pair ((SetCat^op)^op) (@hasProduct _ TransportedCCC)
      BoolS BoolS BoolS id_resp id_resp true = (true, true).
Proof. reflexivity. Qed.

Example transported_eval_computes
  : @Cats.Cat.Exponential.Core.eval ((SetCat^op)^op)
      (@hasProduct _ TransportedCCC) (@hasExponential _ TransportedCCC)
      BoolS BoolS (id_resp, true) = true.
Proof. reflexivity. Qed.

Example transported_curry_computes
  : @curry ((SetCat^op)^op) (@hasProduct _ TransportedCCC)
      (@hasExponential _ TransportedCCC) BoolS BoolS BoolS
      (@Cats.Cat.Product.Core.π2 ((SetCat^op)^op)
        (@hasProduct _ TransportedCCC) BoolS BoolS) false true = true.
Proof. reflexivity. Qed.

Example transported_exponential_inverse_computes
  : (@functor_exponential _ _ E.1 SetCat_CCC TransportedCCC
      (CCCFunctor_IsCCCF (EquivalenceCCCF E SetCat_CCC)) BoolS BoolS).1
      id_resp true = true.
Proof. reflexivity. Qed.
End TransportComputations.
