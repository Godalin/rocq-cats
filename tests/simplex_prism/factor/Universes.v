From Cats Require Import
  Instance.Set.Simplicial.Prism
  Instance.Set.Simplicial.Homotopy.SphereCylinder.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Cylinder Values at Independent Sizes *)

(** ** Strict Profiles

    Keep both strict carrier/equality orders. None of the map or sphere
    clients has Kan choices, algebra structures or equality of functions. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The all-degree factor law only requires a given cylinder map. *)

Definition lower_factor
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (m n : nat)
    (K : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X)
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : K n ({|lower := a|}, {|lower := t|}) ≈S
      X[SimplexPrismIndexF a t]Δ
        (simplex_prism_eval K (simplex_prism_pivot a t))
  := simplex_prism_eval_factor K a t.

(** Staircase values determine equality in every degree. *)

Definition lower_maps
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (m : nat)
    (K L : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X)
  : (K ≈N L) ↔ ∀ k, simplex_prism_eval K k ≈S simplex_prism_eval L k
  := simplex_prism_map_eq_iff K L.

(** The existing actual sphere prism table is consumed unchanged. *)

Definition lower_sphere
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (n : nat) (a : (@Hom Δ) n 2) (t : (@Hom Δ) n 1%nat)
  : two_sphere_cylinder_eval X b H a t ≈S
      X[SimplexPrismIndexF a t]Δ
        (two_sphere_prism H (simplex_prism_pivot a t))
  := two_sphere_cylinder_factor H a t.

(** The all-degree factor law only requires a given cylinder map. *)

Definition higher_factor
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (m n : nat)
    (K : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : K n ({|lower := a|}, {|lower := t|}) ≈S
      X[SimplexPrismIndexF a t]Δ
        (simplex_prism_eval K (simplex_prism_pivot a t))
  := simplex_prism_eval_factor K a t.

(** Staircase values determine equality in every degree. *)

Definition higher_maps
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (m : nat)
    (K L : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
  : (K ≈N L) ↔ ∀ k, simplex_prism_eval K k ≈S simplex_prism_eval L k
  := simplex_prism_map_eq_iff K L.

(** The existing actual sphere prism table is consumed unchanged. *)

Definition higher_sphere
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (n : nat) (a : (@Hom Δ) n 2) (t : (@Hom Δ) n 1%nat)
  : two_sphere_cylinder_eval X b H a t ≈S
      X[SimplexPrismIndexF a t]Δ
        (two_sphere_prism H (simplex_prism_pivot a t))
  := two_sphere_cylinder_factor H a t.

End StrictSizes.
