From Cats Require Export
  Cat.Monad.Strength.
From Cats.Set Require Import
  Constant.
From Cats Require Import
  Cat.Monoidal.Cartesian
  Cat.Product.Transport
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.

Local Open Scope monoidal_scope.

(** * Pointwise Uniqueness of Setoid Strength

    Fix an endofunctor of setoids and a supplied tensorial strength for
    the selected cartesian monoidal structure. Naturality and the unit
    law determine its value on every pair. Keep ambient carrier and
    equality levels independent; no exponential or Monad is needed. *)

(** * 广集强度的逐点唯一性

    固定广集自函子及其在选定笛卡尔幺半结构上的张量强度。自然性和单位律决定
    其在每一对输入上的值。所在载体与相等层级保持独立，不要求指数或 Monad。 *)

Section Pointwise.
Context (F : Fct SetCat SetCat).

(** A fixed ordinary context is paired with the result by the functor's
    action. This compares the supplied strength, without choosing a new
    one or equating its law fields. *)

(** 固定通常上下文由函子作用配到结果旁边；此式比较所给强度，不另选强度，
    也不等同其定律字段。 *)

Lemma set_strength_value `{S : !HasStrength F}
    (X Y : SetC) (x : X) (v : F Y)
  : st[X; Y] (x,v) ≈S fmap F ⟨const[Y] x, id⟩ v.
Proof.
  pose proof (strength_natural (F := F)
    (const[UnitS] x) (id[Y])) as H.
  rewrite !cartesian_tensor_map, fmap_id in H.
  pose proof (H (tt,v)) as Hv.
  change (st[X; Y] (x,v)
    ≈S fmap F (const[UnitS] x × id[Y])
      (st[UnitS; Y] (tt,v))) in Hv.
  etransitivity; [exact Hv |].
  assert (Hm : (const[UnitS] x × id[Y]) ≈
    ⟨const[Y] x, id⟩ ∘ (π2 : Hom (UnitS ×S Y) Y)).
  { intros [[] y]. split; reflexivity. }
  pose proof (strength_unit S Y (tt,v)) as Hu.
  change (fmap F (π2 : Hom (UnitS ×S Y) Y)
    (st[UnitS; Y] (tt,v)) ≈S v) in Hu.
  rewrite Hm, fmap_comp. cbn. rewrite Hu. reflexivity.
Qed.

(** Any other supplied strength has the same components in the specified
    pointwise equality. *)

(** 任意另一个所给强度在指定逐点相等下具有相同分量。 *)

Lemma set_strength_unique
    (S T : HasStrength F) (X Y : SetC)
  : @strengthN _ _ _ S (X, Y) ≈ @strengthN _ _ _ T (X, Y).
Proof.
  intros [x v]. rewrite !set_strength_value. reflexivity.
Qed.

End Pointwise.

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
Context (F : Fct (SetCat@{u p _ _ _ _ _})
    (SetCat@{u p _ _ _ _ _})).

(** Pair a fixed ordinary context with every functor result. Respectfulness
    uses the functor on both equal pairing maps and equal effectful values. *)

(** 将固定通常上下文配到函子结果旁。尊重性分别使用函子保持配对映射相等与
    带效应值相等。 *)

Program Definition set_strength_map (X Y : SetC)
  : (X ×S F Y) →r F (X ×S Y)
  :=
  {|func p := fmap F ⟨const[Y] (fst p), id⟩ (snd p)
  |}.
Next Obligation.
  intros [x v] [y w] [E H].
  transitivity (fmap F ⟨const[Y] y, id⟩ v).
  - apply (fmap_proper (obj := F)).
    intros a. split; [exact E|reflexivity].
  - apply func_proper. exact H.
Defined.

(** These maps are natural in both variables. Compare the derived tensor
    action with the selected product map before using functor composition. *)

(** 这些映射对两个变量自然；先比较派生张量作用与选定积映射，再使用函子复合。 *)

Program Definition SetStrengthN
  : tensorF ∘F (IdF ×F F) ⇒ F ∘F tensorF
  :=
  {|nt p := set_strength_map (fst p) (snd p)
  |}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  intros [x v].
  change (fmap F ⟨const[Y2] (f x), id⟩ (fmap F g v) ≈S
    fmap F (tensor_map (C := SetCat) f g) (fmap F ⟨const[X2] x, id⟩ v)).
  rewrite cartesian_tensor_map.
  assert (H : ⟨const[Y2] (f x), id⟩ ∘ g
    ≈ (f × g) ∘ ⟨const[X2] x, id⟩).
  { intros y. split; reflexivity. }
  pose proof (fmap_proper (obj := F) _ _ H v) as E.
  rewrite !fmap_comp in E. exact E.
Qed.

(** The selected strength satisfies the unit and associativity diagrams by
    functor identity and composition. It is unique by [set_strength_unique]. *)

(** 所选强度由函子恒等及复合律满足单位及结合图，由 [set_strength_unique] 唯一。 *)

Program Definition SetStrength
  : HasStrength F
  :=
  {|strengthN := SetStrengthN
  |}.
Next Obligation.
  intros [[] v].
  change (fmap F (π2 : UnitS ×S Y →r Y)
    (fmap F ⟨const[Y] (tt : UnitS), id⟩ v) ≈S v).
  assert (H : (π2 : Hom[SetCat] (UnitS ×S Y) Y) ∘ ⟨const[Y] (tt : UnitS), id⟩
    ≈ id[Y]).
  { intros y. reflexivity. }
  pose proof (fmap_proper (obj := F) _ _ H v) as E.
  rewrite fmap_comp, fmap_id in E. exact E.
Defined.

Next Obligation.
  intros [[x y] v].
  change (fmap F product_assoc.1 (fmap F ⟨const[Z] (x,y), id⟩ v) ≈S
    fmap F ⟨const[Y ×S Z] x, id⟩ (fmap F ⟨const[Z] y, id⟩ v)).
  assert (H : product_assoc.1 ∘ ⟨const[Z] (x,y), id⟩
    ≈ ⟨const[Y ×S Z] x, id⟩ ∘ ⟨const[Z] y, id⟩).
  { intros z. split; [reflexivity | split; reflexivity]. }
  pose proof (fmap_proper (obj := F) _ _ H v) as E.
  rewrite !fmap_comp in E. exact E.
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
Local Open Scope monad_scope.
Universes u p.
Context (M : Monad (SetCat@{u p _ _ _ _ _})).

(** Give the supplied Monad its canonical setoid strength. Both compatibility
    diagrams follow from naturality, without commutativity or exponentials. *)

(** 赋予所给 Monad 规范广集强度；两张相容图由自然性推出，不要求交换性或指数。 *)

Program Definition SetStrongM
  : StrongMonad SetCat
  := StrongMonadOfMonad M (SetStrength M)
    {|strongmonad_unit := _
    ; strongmonad_mul := _
    |}.
Next Obligation.
  intros [x y].
  change (fmap M ⟨const[Y] x, id⟩ (η[M] Y y) ≈S
    η[M] (X ×S Y) (x,y)).
  symmetry. exact (nat_naturality (η[M]) ⟨const[Y] x, id⟩ y).
Qed.

Next Obligation.
  intros [x v].
  change (fmap M ⟨const[Y] x, id⟩ (μ[M] Y v)
    ≈S μ[M] (X ×S Y) (fmap M (set_strength_map M X Y)
      (fmap M ⟨const[M Y] x, id⟩ v))).
  transitivity (μ[M] (X ×S Y)
    (fmap M (fmap M ⟨const[Y] x, id⟩) v)).
  - symmetry.
    exact (nat_naturality (μ[M]) ⟨const[Y] x, id⟩ v).
  - apply func_proper.
    assert (H : fmap M ⟨const[Y] x, id⟩
      ≈ (set_strength_map M X Y : Hom[SetCat] _ _)
        ∘ ⟨const[M Y] x, id⟩).
    { intros w. reflexivity. }
    pose proof (fmap_proper (obj := M) _ _ H v) as E.
    rewrite fmap_comp in E. exact E.
Qed.

End Monads.
