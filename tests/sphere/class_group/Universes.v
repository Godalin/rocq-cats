From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independently Sized Groups and Inverse Witnesses

    Keep simplex equality strictly below or above its carrier. All model
    choices are explicit; inherited inverse theory must remain
    usable on the very same generated class setoid. *)

(** ** Strict Levels

    Fix three strictly increasing levels. Check each interface at both
    the lower and higher equality level, without resizing witnesses. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The existing Semigroup interface retains independently sized classes. *)

Definition lower_semigroup
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Semigroup
  := TwoSphereClassSemigroup X b H.

(** The existing Monoid interface retains independently sized classes. *)

Definition lower_monoid
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Monoid
  := TwoSphereClassMonoid X b H.

(** The existing Group interface retains independently sized classes. *)

Definition lower_group
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : Group
  := TwoSphereClassGroup X b H K L.

(** General monoid uniqueness compares independent candidate choices. *)

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

Definition lower_inverse_resp
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := @inv_resp (TwoSphereClassGroup X b H K L).

(** Six independent choices induce pointwise equal inverse maps. *)

Definition lower_choice
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H H' : HasHornFillers X 3 fin_first⁺⁺)
    (K K' : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L L' : HasHornFillers X 3 fin_first⁺)
  : @inv_resp (TwoSphereClassGroup X b H K L) ≈f
      @inv_resp (TwoSphereClassGroup X b H' K' L')
  := two_sphere_class_group_inverse_choice_eq X b H H' K K' L L'.

(** A supplied left inverse is compared by existing group uniqueness. *)

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
  : y ≈S @inv _ _ _ (hasInverse (TwoSphereClassGroup X b H K L)) x
  := @inv_unique (TwoSphereClassGroup X b H K L) x y E.

(** The existing Semigroup interface retains independently sized classes. *)

Definition higher_semigroup
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Semigroup
  := TwoSphereClassSemigroup X b H.

(** The existing Monoid interface retains independently sized classes. *)

Definition higher_monoid
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Monoid
  := TwoSphereClassMonoid X b H.

(** The existing Group interface retains independently sized classes. *)

Definition higher_group
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : Group
  := TwoSphereClassGroup X b H K L.

(** General monoid uniqueness compares independent candidate choices. *)

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

Definition higher_inverse_resp
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := @inv_resp (TwoSphereClassGroup X b H K L).

(** Six independent choices induce pointwise equal inverse maps. *)

Definition higher_choice
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H H' : HasHornFillers X 3 fin_first⁺⁺)
    (K K' : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L L' : HasHornFillers X 3 fin_first⁺)
  : @inv_resp (TwoSphereClassGroup X b H K L) ≈f
      @inv_resp (TwoSphereClassGroup X b H' K' L')
  := two_sphere_class_group_inverse_choice_eq X b H H' K K' L L'.

(** A supplied left inverse is compared by existing group uniqueness. *)

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
  : y ≈S @inv _ _ _ (hasInverse (TwoSphereClassGroup X b H K L)) x
  := @inv_unique (TwoSphereClassGroup X b H K L) x y E.

End StrictSizes.
