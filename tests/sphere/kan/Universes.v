From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereKan.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and Minimal Three-Horn Choices

    Every operation accepts only its required horn selection. The probes
    keep ambient equality strictly below or above simplex carriers, without
    shrinking retained tetrahedra or requiring full Kan choices. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Actual gluing at lower ambient equality. *)

Definition lower_horn
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (i : Ordinal 3) (a : Ordinal 3 → TwoSphereS X b)
  : HornS X 3 i
  := SphereTetrahedronHornN X b i a.

(** Composite only needs missing face 2, at lower equality. *)

Definition lower_composite
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺}
    (x y : TwoSphereS X b)
  : ∃ z : TwoSphereS X b, TwoSphereComposite X b x y z
  := SphereKanComposite X b x y.

(** RightInverse only needs missing face 1, at lower equality. *)

Definition lower_rightinverse
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b x y (two_sphere_base X b)
  := SphereKanRightInverse X b x.

(** LeftInverse only needs missing face 3, at lower equality. *)

Definition lower_leftinverse
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b y x (two_sphere_base X b)
  := SphereKanLeftInverse X b x.

(** Actual gluing at higher ambient equality. *)

Definition higher_horn
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (i : Ordinal 3) (a : Ordinal 3 → TwoSphereS X b)
  : HornS X 3 i
  := SphereTetrahedronHornN X b i a.

(** Composite only needs missing face 2, at higher equality. *)

Definition higher_composite
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺}
    (x y : TwoSphereS X b)
  : ∃ z : TwoSphereS X b, TwoSphereComposite X b x y z
  := SphereKanComposite X b x y.

(** RightInverse only needs missing face 1, at higher equality. *)

Definition higher_rightinverse
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b x y (two_sphere_base X b)
  := SphereKanRightInverse X b x.

(** LeftInverse only needs missing face 3, at higher equality. *)

Definition higher_leftinverse
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b y x (two_sphere_base X b)
  := SphereKanLeftInverse X b x.

End StrictSizes.
