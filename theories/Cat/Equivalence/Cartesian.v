From Cats Require Export
  Cat.Equivalence.Adjunction.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Cat.Terminal
  Cat.Product.Core
  Cat.Functor.Cartesian
  Cat.Limit.Core
  Cat.Limit.Terminal
  Cat.Limit.Product
  Cat.Limit.Equivalence.

(** * Cartesian Structure along Specified Equivalences

    Empty and pair-shaped limits select the transported terminal and product
    structures. The universal-property proofs are the general limit proofs. *)

(** * 沿指定等价运输笛卡尔结构

    空形状与对象对形状的极限选择运输后的终对象和积结构；泛性质证明即为
    一般极限证明。 *)

Local Open Scope cat_scope.
Local Open Scope hom_scope.

Section QuasiInverseCartesian.
Context {C D : Cat} (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF).

(** Transfer a selected terminal object via the general empty-limit
    construction. No products or exponentials are required. *)

(** 通过一般空极限构造运输选定终对象，无需积或指数。 *)

Definition QuasiInverseHasTerminal `{TC : !HasTerminal C}
  : HasTerminal D
  := @EmptyLimitsTerminal D
      (@QuasiInverseLimits C D F G u v EmptyShape (@TerminalLimits C TC)).

(** Transfer selected products via pair-shaped limits, independently of
    terminal or exponential choices. *)

(** 通过对象对形状的极限运输选定积，独立于终对象或指数的选择。 *)

Definition QuasiInverseHasProduct `{PC : !HasProduct C}
  : HasProduct D
  := @PairLimitsProduct D
      (@QuasiInverseLimits C D F G u v PairShape (@ProductLimits C PC)).

(** Both terminal and product preservation follow from the constructed
    right adjunction, for arbitrary specified source choices. *)

(** 对任意指定来源选择，终对象和积的保持性都来自构造得到的右伴随。 *)

Program Definition QuasiInverseIsCartesianF
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
  : IsCartesianF F TC PC
  :=
  {|functor_terminal := right_adjoint_preserves_terminal
      (QuasiInverseAdjunction G F v u) (@terminal_universal C TC)
  ; functor_product X Y := right_adjoint_preserves_product
      (QuasiInverseAdjunction G F v u) (@product_universal C PC X Y)
  |}.

(** The bundled view keeps the original functor and preservation witnesses. *)

(** 打包视图保留原函子及保持见证。 *)

Definition QuasiInverseCartesianF
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
  : @CartesianFunctor C D TC PC
  := CartesianFunctorFromPreservation F QuasiInverseIsCartesianF.

(** The transported first projection has the expected component formula. *)

(** 运输后的第一投影具有预期的分量公式。 *)

Lemma quasi_inverse_product_π1 `{PC : !HasProduct C} (X Y : @Ob D)
  : @Cats.Cat.Product.Core.π1 D QuasiInverseHasProduct X Y ≈
      v.1 X ∘ fmap F (@Cats.Cat.Product.Core.π1 C PC (G X) (G Y)).
Proof. reflexivity. Qed.

(** The second projection uses the same supplied target isomorphism. *)

(** 第二投影使用同一个给定目标同构。 *)

Lemma quasi_inverse_product_π2 `{PC : !HasProduct C} (X Y : @Ob D)
  : @Cats.Cat.Product.Core.π2 D QuasiInverseHasProduct X Y ≈
      v.1 Y ∘ fmap F (@Cats.Cat.Product.Core.π2 C PC (G X) (G Y)).
Proof. reflexivity. Qed.

End QuasiInverseCartesian.

(** The chosen terminal structure transported along an ordinary equivalence. *)

(** 沿通常范畴等价运输的选定终对象结构。 *)

Definition EquivalenceHasTerminal {C D : Cat} (e : C ≃C D)
    `{TC : !HasTerminal C}
  : HasTerminal D
  := QuasiInverseHasTerminal e.1 e.2.1 (fst e.2.2) (snd e.2.2).

(** The chosen product structure transported along that equivalence. *)

(** 沿同一等价运输的选定积结构。 *)

Definition EquivalenceHasProduct {C D : Cat} (e : C ≃C D)
    `{PC : !HasProduct C}
  : HasProduct D
  := QuasiInverseHasProduct e.1 e.2.1 (fst e.2.2) (snd e.2.2).
