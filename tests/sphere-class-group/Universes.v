From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independently Sized Groups and Inverse Witnesses

    Keep simplex equality strictly below or above its carrier. All model
    choices are explicit; inherited group inverse theory must remain
    usable on the very same generated class setoid. *)

(** * 大小独立的群与逆见证

    单形相等严格低于或高于载体；所有模型选择均显式给出。继承的一般群逆理论
    须在完全相同的生成类广集上保持可用。 *)

(** ** Strict Levels

    Fix three strictly increasing levels. Check each interface at both
    the lower and higher equality level, without resizing witnesses. *)

(** ** 严格层级

    固定三个严格递增层级；每个接口均在较低及较高相等层级检查，不重设见证大小。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The existing Semigroup interface retains independently sized classes. *)

(** 既有 Semigroup 接口保留大小独立的类。 *)

Definition lower_semigroup
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Semigroup (TwoSphereClassS X b)
  := TwoSphereClassSemigroup X b H.

(** The existing Monoid interface retains independently sized classes. *)

(** 既有 Monoid 接口保留大小独立的类。 *)

Definition lower_monoid
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Monoid (TwoSphereClassS X b)
  := TwoSphereClassMonoid X b H.

(** The existing Group interface retains independently sized classes. *)

(** 既有 Group 接口保留大小独立的类。 *)

Definition lower_group
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : Group (TwoSphereClassS X b)
  := TwoSphereClassGroup X b H K L.

(** General monoid uniqueness compares independent candidate choices. *)

(** 一般幺半群唯一性比较独立候选选择。 *)

Definition lower_candidates
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : ((@SphereKanLeftInverse X b K x).1 : TwoSphereClassS X b) ≈S
      (@SphereKanRightInverse X b L x).1
  := two_sphere_inverse_candidates_eq X b H K L x.

(** Reuse the generic respectful inverse map directly. *)

(** 直接复用通用保相等逆映射。 *)

Definition lower_inverse_resp
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := @group_inv_resp _ (TwoSphereClassGroup X b H K L).

(** Six independent choices induce pointwise equal inverse maps. *)

(** 六个独立选择给出逐点相等逆映射。 *)

Definition lower_choice
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H H' : HasHornFillers X 3 fin_first⁺⁺)
    (K K' : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L L' : HasHornFillers X 3 fin_first⁺)
  : @group_inv_resp _ (TwoSphereClassGroup X b H K L) ≈f
      @group_inv_resp _ (TwoSphereClassGroup X b H' K' L')
  := two_sphere_class_group_inverse_choice_eq X b H H' K K' L L'.

(** A supplied left inverse is compared by existing group uniqueness. *)

(** 由既有群唯一性比较给定左逆。 *)

Definition lower_unique
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
    (x y : TwoSphereClassS X b)
    (E : two_sphere_kan_mul X b H y x ≈S
      (two_sphere_base X b : TwoSphereClassS X b))
  : y ≈S @group_inv _ (TwoSphereClassGroup X b H K L) x
  := @group_inv_unique _ (TwoSphereClassGroup X b H K L) x y E.

(** The existing Semigroup interface retains independently sized classes. *)

(** 既有 Semigroup 接口保留大小独立的类。 *)

Definition higher_semigroup
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Semigroup (TwoSphereClassS X b)
  := TwoSphereClassSemigroup X b H.

(** The existing Monoid interface retains independently sized classes. *)

(** 既有 Monoid 接口保留大小独立的类。 *)

Definition higher_monoid
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Monoid (TwoSphereClassS X b)
  := TwoSphereClassMonoid X b H.

(** The existing Group interface retains independently sized classes. *)

(** 既有 Group 接口保留大小独立的类。 *)

Definition higher_group
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : Group (TwoSphereClassS X b)
  := TwoSphereClassGroup X b H K L.

(** General monoid uniqueness compares independent candidate choices. *)

(** 一般幺半群唯一性比较独立候选选择。 *)

Definition higher_candidates
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : ((@SphereKanLeftInverse X b K x).1 : TwoSphereClassS X b) ≈S
      (@SphereKanRightInverse X b L x).1
  := two_sphere_inverse_candidates_eq X b H K L x.

(** Reuse the generic respectful inverse map directly. *)

(** 直接复用通用保相等逆映射。 *)

Definition higher_inverse_resp
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := @group_inv_resp _ (TwoSphereClassGroup X b H K L).

(** Six independent choices induce pointwise equal inverse maps. *)

(** 六个独立选择给出逐点相等逆映射。 *)

Definition higher_choice
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H H' : HasHornFillers X 3 fin_first⁺⁺)
    (K K' : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L L' : HasHornFillers X 3 fin_first⁺)
  : @group_inv_resp _ (TwoSphereClassGroup X b H K L) ≈f
      @group_inv_resp _ (TwoSphereClassGroup X b H' K' L')
  := two_sphere_class_group_inverse_choice_eq X b H H' K K' L L'.

(** A supplied left inverse is compared by existing group uniqueness. *)

(** 由既有群唯一性比较给定左逆。 *)

Definition higher_unique
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
    (x y : TwoSphereClassS X b)
    (E : two_sphere_kan_mul X b H y x ≈S
      (two_sphere_base X b : TwoSphereClassS X b))
  : y ≈S @group_inv _ (TwoSphereClassGroup X b H K L) x
  := @group_inv_unique _ (TwoSphereClassGroup X b H K L) x y E.

End StrictSizes.
