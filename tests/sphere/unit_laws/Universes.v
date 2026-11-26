From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereUnit.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Minimal Choices and Independent Sizes for Unit Laws

    Separate the simplex carrier from lower and higher equality levels.
    Degenerate unit witnesses need no choices. The class laws use only
    missing-face-two output comparison, with independent explicit choices
    for multiplication and the relevant inverse candidate. *)

(** ** Strict Levels

    Fix three strictly increasing levels; each public construction/law is
    tested with simplex equality at the lower and higher level. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The left unit tetrahedron needs no selected filler. *)

Definition lower_left_witness
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b (two_sphere_base X b) x x
  := SphereLeftUnitComposite X b x.

(** The right unit tetrahedron needs no selected filler. *)

Definition lower_right_witness
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b x (two_sphere_base X b) x
  := SphereRightUnitComposite X b x.

(** The left unit law uses only output comparison and multiplication. *)

Definition lower_unit_l
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_base X b) x ≈S x
  := two_sphere_kan_mul_unit_l X b H x.

(** The right unit law uses only output comparison and multiplication. *)

Definition lower_unit_r
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (two_sphere_base X b) ≈S x
  := two_sphere_kan_mul_unit_r X b H x.

(** The left candidate needs only its own three-horn choice. *)

Definition lower_inverse_l
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (@SphereKanLeftInverse X b K x).1 x ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_l X b H K x.

(** The right candidate needs only its own three-horn choice. *)

Definition lower_inverse_r
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (@SphereKanRightInverse X b K x).1 ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_r X b H K x.

(** The left unit tetrahedron needs no selected filler. *)

Definition higher_left_witness
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b (two_sphere_base X b) x x
  := SphereLeftUnitComposite X b x.

(** The right unit tetrahedron needs no selected filler. *)

Definition higher_right_witness
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b x (two_sphere_base X b) x
  := SphereRightUnitComposite X b x.

(** The left unit law uses only output comparison and multiplication. *)

Definition higher_unit_l
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_base X b) x ≈S x
  := two_sphere_kan_mul_unit_l X b H x.

(** The right unit law uses only output comparison and multiplication. *)

Definition higher_unit_r
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (two_sphere_base X b) ≈S x
  := two_sphere_kan_mul_unit_r X b H x.

(** The left candidate needs only its own three-horn choice. *)

Definition higher_inverse_l
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (@SphereKanLeftInverse X b K x).1 x ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_l X b H K x.

(** The right candidate needs only its own three-horn choice. *)

Definition higher_inverse_r
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (@SphereKanRightInverse X b K x).1 ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_r X b H K x.

End StrictSizes.
