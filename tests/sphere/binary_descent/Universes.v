From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMagma
  Instance.Set.Magma.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and Explicit Choices for Binary Descent

    Probe both equality sizes below and above the simplex carrier size.
    Supplied composites need no three-horn selection; raw multiplication
    needs only its explicit three-horn choice. Magma packaging uses the
    same minimal four-dimensional selections as the two transports. *)

(** ** Strictly Separated Levels

    Fix three strictly increasing levels. Each interface below is checked
    once at the lower equality level and once at the higher level. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Two generated inputs transport supplied composites in both directions. *)

Definition lower_transport
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z : TwoSphereS X b)
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y' z
  := two_sphere_composite_class X b E F z.

(** Supplied composites can be compared without a dimension-three choice. *)

Definition lower_comparison
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x' y' z')
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : (z : TwoSphereClassS X b) ≈S z'
  := two_sphere_composite_output_class_eq X b H K E F.

(** Raw multiplication requires only its explicit three-horn choice. *)

Definition lower_raw_mul
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : TwoSphereClassS X b → TwoSphereClassS X b → TwoSphereClassS X b
  := two_sphere_kan_mul X b H.

(** The chosen magma uses the same independently sized class setoid. *)

Definition lower_magma
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Magma
  := TwoSphereClassMagma X b H.

(** Independent three-horn choices give equal product-setoid maps. *)

Definition lower_choice
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
  : set_magma_mul_resp (TwoSphereClassMagma X b H) ≈f
      set_magma_mul_resp (TwoSphereClassMagma X b K)
  := two_sphere_class_magma_choice_eq X b H K.

(** Two generated inputs transport supplied composites in both directions. *)

Definition higher_transport
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z : TwoSphereS X b)
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y' z
  := two_sphere_composite_class X b E F z.

(** Supplied composites can be compared without a dimension-three choice. *)

Definition higher_comparison
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x' y' z')
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : (z : TwoSphereClassS X b) ≈S z'
  := two_sphere_composite_output_class_eq X b H K E F.

(** Raw multiplication requires only its explicit three-horn choice. *)

Definition higher_raw_mul
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : TwoSphereClassS X b → TwoSphereClassS X b → TwoSphereClassS X b
  := two_sphere_kan_mul X b H.

(** The chosen magma uses the same independently sized class setoid. *)

Definition higher_magma
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Magma
  := TwoSphereClassMagma X b H.

(** Independent three-horn choices give equal product-setoid maps. *)

Definition higher_choice
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
  : set_magma_mul_resp (TwoSphereClassMagma X b H) ≈f
      set_magma_mul_resp (TwoSphereClassMagma X b K)
  := two_sphere_class_magma_choice_eq X b H K.

End StrictSizes.
