From Cats Require Export
  Cat.Monoidal.Strength.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Monoidal.Cartesian
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope monoidal_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

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

Lemma set_strength_value (S : HasStrength SetCartesianMonoidal F)
    (X Y : SetC) (x : X) (v : F Y)
  : st[S; X; Y] (x,v) ≈S fmap F ⟨const_resp Y x, id⟩ v.
Proof.
  pose proof (strength_natural S (const_resp UnitS x) (@id Y)) as H.
  unfold SetCartesianMonoidal in H.
  rewrite !cartesian_tensor_map, functor_id in H.
  pose proof (H (tt,v)) as Hv.
  change (st[S; X; Y] (x,v) ≈S
    fmap F (const_resp UnitS x × @id Y) (st[S; UnitS; Y] (tt,v))) in Hv.
  etransitivity; [exact Hv |].
  assert (Hm : (const_resp UnitS x × @id Y) ≈
    ⟨const_resp Y x, id⟩ ∘ (π2 : Hom (UnitS ×S Y) Y)).
  { intros [[] y]. split; reflexivity. }
  pose proof (strength_unit S Y (tt,v)) as Hu.
  change (fmap F (π2 : Hom (UnitS ×S Y) Y)
    (st[S; UnitS; Y] (tt,v)) ≈S v) in Hu.
  etransitivity.
  - exact (@functor_fmap_proper SetCat SetCat F _ _ _ _ Hm (st[S; UnitS; Y] (tt,v))).
  - etransitivity.
    + exact (@functor_comp SetCat SetCat F _ _ _ ⟨const_resp Y x, id⟩
        (π2 : Hom (UnitS ×S Y) Y) (st[S; UnitS; Y] (tt,v))).
    + exact (@func_proper (F Y) (F (X ×S Y))
        (fmap F ⟨const_resp Y x, id⟩) _ _ Hu).
Qed.

(** Any other supplied strength has the same components in the specified
    pointwise equality. *)

(** 任意另一个所给强度在指定逐点相等下具有相同分量。 *)

Lemma set_strength_unique (S T : HasStrength SetCartesianMonoidal F)
    (X Y : SetC)
  : st[S; X; Y] ≈ st[T; X; Y].
Proof.
  intros [x v]. rewrite !set_strength_value. reflexivity.
Qed.

End Pointwise.
