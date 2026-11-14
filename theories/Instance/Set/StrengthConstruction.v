From Cats Require Export
  Instance.Set.Strength
  Cat.Monad.Strength.
From Cats Require Import
  Cat.Core
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid
  Cat.Monoidal.Cartesian
  Cat.Product.Transport.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope monoidal_scope.
Local Open Scope monad_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Canonical Strength on Setoids

    Fix an endofunctor of one setoid category, retaining independent carrier
    and equality levels. Map pairing with a fixed context value through the
    functor. Prove naturality and monoidal coherence, then explicitly choose
    the resulting strength. Importing this construction selects no instance. *)

(** * 广集上的规范强度

    固定同一个广集范畴的自函子，保留独立载体及相等层级。通过函子映射与固定
    上下文值的配对，证明自然性及幺半相干后显式选择此强度。导入不选取实例。 *)

Section Construction.
Universes u p.
Context (F : Functor (SetCat@{u p _ _ _ _ _})
    (SetCat@{u p _ _ _ _ _})).

(** Pair a fixed ordinary context with every functor result. Respectfulness
    uses the functor on both equal pairing maps and equal effectful values. *)

(** 将固定通常上下文配到函子结果旁。尊重性分别使用函子保持配对映射相等与
    带效应值相等。 *)

Program Definition set_strength_map (X Y : SetC)
  : (X ×S F Y) →r F (X ×S Y)
  :=
  {|func p := fmap F ⟨const_resp Y (fst p), id⟩ (snd p)
  |}.
Next Obligation.
  intros [x v] [y w] [E H].
  transitivity (fmap F ⟨const_resp Y y, id⟩ v).
  - apply (@functor_fmap_proper SetCat SetCat F _ _).
    intros a. split; [exact E|reflexivity].
  - apply func_proper. exact H.
Defined.

(** These maps are natural in both variables. Compare the derived tensor
    action with the selected product map before using functor composition. *)

(** 这些映射对两个变量自然；先比较派生张量作用与选定积映射，再使用函子复合。 *)

Program Definition SetStrengthN
  : (tensorF SetCartesianMonoidal ∘F (IdF ×F F)) ⇒
    (F ∘F tensorF SetCartesianMonoidal)
  :=
  {|nt p := set_strength_map (fst p) (snd p)
  |}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  intros [x v].
  change (fmap F ⟨const_resp Y2 (f x), id⟩ (fmap F g v) ≈S
    fmap F (@tensor_map SetCat SetCartesianMonoidal _ _ _ _ f g)
      (fmap F ⟨const_resp X2 x, id⟩ v)).
  transitivity (fmap F (f × g) (fmap F ⟨const_resp X2 x, id⟩ v)).
  - transitivity (fmap F (⟨const_resp Y2 (f x), id⟩ ∘ g) v).
    + symmetry. exact (@functor_comp SetCat SetCat F _ _ _ _ _ v).
    + transitivity (fmap F ((f × g) ∘ ⟨const_resp X2 x, id⟩) v).
      * apply (@functor_fmap_proper SetCat SetCat F _ _).
        intros y. split; reflexivity.
      * exact (@functor_comp SetCat SetCat F _ _ _ _ _ v).
  - symmetry. exact (@functor_fmap_proper SetCat SetCat F _ _ _ _
      (@cartesian_tensor_map SetCat SetCat_HasTerminal SetCat_HasProduct
        _ _ _ _ f g) (fmap F ⟨const_resp X2 x, id⟩ v)).
Defined.

(** The selected strength satisfies the unit and associativity diagrams by
    functor identity and composition. It is unique by [set_strength_unique]. *)

(** 所选强度由函子恒等及复合律满足单位及结合图，由 [set_strength_unique] 唯一。 *)

Program Definition SetStrength
  : HasStrength SetCartesianMonoidal F
  :=
  {|strengthN := SetStrengthN
  |}.
Next Obligation.
  intros [[] v].
  change (fmap F (π2 : UnitS ×S Y →r Y)
    (fmap F ⟨@const_resp Y UnitS tt, id⟩ v) ≈S v).
  transitivity (fmap F (@id Y) v).
  - transitivity (fmap F ((π2 : UnitS ×S Y →r Y) ∘
      ⟨@const_resp Y UnitS tt, id⟩) v).
    + symmetry. exact (@functor_comp SetCat SetCat F _ _ _ _ _ v).
    + apply (@functor_fmap_proper SetCat SetCat F _ _).
      intros y. reflexivity.
  - exact (@functor_id SetCat SetCat F Y v).
Defined.

Next Obligation.
  intros [[x y] v].
  change (fmap F (@product_assoc SetCat SetCat_HasProduct X Y Z).1
    (fmap F ⟨const_resp Z (x,y), id⟩ v) ≈S
    fmap F ⟨const_resp (Y ×S Z) x, id⟩
      (fmap F ⟨const_resp Z y, id⟩ v)).
  transitivity (fmap F ((@product_assoc SetCat SetCat_HasProduct X Y Z).1 ∘
    ⟨const_resp Z (x,y), id⟩) v).
  - symmetry. exact (@functor_comp SetCat SetCat F _ _ _ _ _ v).
  - transitivity (fmap F (⟨const_resp (Y ×S Z) x, id⟩ ∘
      ⟨const_resp Z y, id⟩) v).
    + apply (@functor_fmap_proper SetCat SetCat F _ _).
      intros z. split; [reflexivity|split; reflexivity].
    + exact (@functor_comp SetCat SetCat F _ _ _ _ _ v).
Defined.

End Construction.

(** * Ordinary Setoid Monads with Canonical Strength

    Fix an ordinary Monad on the same setoid category. Naturality of its
    unit and multiplication makes both compatible with the canonical
    strength. Keep the original Monad as the unique parent and expose an
    explicit strong view; no new Monad laws are assumed or reproved. *)

(** * 带规范强度的通常广集 Monad

    固定同一广集范畴上的通常 Monad。单位及乘法的自然性使二者与规范强度相容。
    保留原 Monad 为唯一父结构，显式给出强视图，不假设或重证新的 Monad 定律。 *)

Section Monads.
Universes u p.
Context (M : Monad (SetCat@{u p _ _ _ _ _})).

(** Give the supplied Monad its canonical setoid strength. Both compatibility
    diagrams follow from naturality, without commutativity or exponentials. *)

(** 赋予所给 Monad 规范广集强度；两张相容图由自然性推出，不要求交换性或指数。 *)

Program Definition SetStrongM
  : StrongMonad SetCat SetCartesianMonoidal
  :=
  {|StrongMonadM := M
  ; hasStrength := SetStrength M
  |}.
Next Obligation.
  intros [x y].
  change (fmap M ⟨const_resp Y x, id⟩ (η[M] Y y) ≈S
    η[M] (X ×S Y) (x,y)).
  symmetry. exact (nt_naturality (η[M]) ⟨const_resp Y x, id⟩ y).
Defined.

Next Obligation.
  intros [x v].
  change (fmap M ⟨const_resp Y x, id⟩ (μ[M] Y v) ≈S
    μ[M] (X ×S Y) (fmap M (set_strength_map M X Y)
      (fmap M ⟨const_resp (M Y) x, id⟩ v))).
  transitivity (μ[M] (X ×S Y)
    (fmap M (fmap M ⟨const_resp Y x, id⟩) v)).
  - symmetry. exact (nt_naturality (μ[M]) ⟨const_resp Y x, id⟩ v).
  - apply (@func_proper _ _ (μ[M] (X ×S Y))).
    transitivity (fmap M (set_strength_map M X Y ∘
      ⟨const_resp (M Y) x, id⟩) v).
    + apply (@functor_fmap_proper SetCat SetCat M _ _).
      intros w. reflexivity.
    + exact (@functor_comp SetCat SetCat M _ _ _ _ _ v).
Defined.

End Monads.
