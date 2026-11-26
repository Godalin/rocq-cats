From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereSecondTransport.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes for Second-Input Descent

    Probe lower and higher simplex equality sizes. Elementary directions
    use different minimal four-horn choices; generated transport retains
    its full witness type and needs no three-horn selection. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Forward transport needs only missing-face-four fillers. *)

Definition lower_forward
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x y y' z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite X b x y' z
  := SphereCompositeSecondHomotopy X b G H.

(** Backward transport needs only missing-face-three fillers. *)

Definition lower_backward
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y y' z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y' z)
  : TwoSphereComposite X b x y z
  := SphereCompositeSecondHomotopyBack X b G H.

(** An actual supplied filler requires no selected structure. *)

Definition lower_given_filler
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y y' z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y z)
    (V : X 4) (HV : is_horn_filler (SphereSecondForwardHornN X b G H) V)
  : TwoSphereComposite X b x y' z
  := SphereCompositeSecondOfFiller X b G H V HV.

(** Generated second-input equality retains two-way computational transport. *)

Definition lower_generated
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x y y' z : TwoSphereS X b) (E : (y : TwoSphereClassS X b) ≈S y')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x y' z
  := two_sphere_composite_second_class X b E x z.

(** The second partial operation is an actual respectful class map. *)

Definition lower_partial
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    `{HXcompare : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereS X b)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := two_sphere_kan_composite_second_resp X b H x.

(** Forward transport needs only missing-face-four fillers. *)

Definition higher_forward
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x y y' z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite X b x y' z
  := SphereCompositeSecondHomotopy X b G H.

(** Backward transport needs only missing-face-three fillers. *)

Definition higher_backward
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y y' z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y' z)
  : TwoSphereComposite X b x y z
  := SphereCompositeSecondHomotopyBack X b G H.

(** An actual supplied filler requires no selected structure. *)

Definition higher_given_filler
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y y' z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y z)
    (V : X 4) (HV : is_horn_filler (SphereSecondForwardHornN X b G H) V)
  : TwoSphereComposite X b x y' z
  := SphereCompositeSecondOfFiller X b G H V HV.

(** Generated second-input equality retains two-way computational transport. *)

Definition higher_generated
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x y y' z : TwoSphereS X b) (E : (y : TwoSphereClassS X b) ≈S y')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x y' z
  := two_sphere_composite_second_class X b E x z.

(** The second partial operation is an actual respectful class map. *)

Definition higher_partial
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    `{HXcompare : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereS X b)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := two_sphere_kan_composite_second_resp X b H x.

End StrictSizes.
