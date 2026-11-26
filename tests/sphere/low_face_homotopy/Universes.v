From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereFaceHomotopy.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Face Conversion with Independent Sizes and Minimal Choices

    The supplied-filler interface has no selection assumption. The chosen
    interface asks only for missing face one in dimension four. Check both
    with simplex equality strictly below and strictly above its carrier. *)

(** ** Strict Profiles

    Fix three strictly increasing bounds, without any global Kan choice. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The actual horn retains the independent value/equality profile. *)

Definition lower_horn
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : HornS X 4 fin_first⁺
  := SphereLowHomotopyHornN X b H.

(** A supplied actual filler needs no chosen filling structure. *)

Definition lower_supplied
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
    (V : X 4) (HV : is_horn_filler (SphereLowHomotopyHornN X b H) V)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopyOfFiller X b H V HV.

(** Only the single four-dimensional horn choice is assumed. *)

Definition lower_chosen
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopy X b H.

(** Descent uses the same actual conversion and generated relation. *)

Definition lower_class
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_low_homotopy_class X b H.

(** Endpoint respectfulness does not require any selected filler. *)

Definition lower_endpoints
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x x' y y' : TwoSphereS X b) (E : x ≈S x') (F : y ≈S y')
  : TwoSphereLowHomotopy X b x y ↔ TwoSphereLowHomotopy X b x' y'
  := TwoSphereLowHomotopy_proper X b x x' E y y' F.

(** The actual horn retains the independent value/equality profile. *)

Definition higher_horn
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : HornS X 4 fin_first⁺
  := SphereLowHomotopyHornN X b H.

(** A supplied actual filler needs no chosen filling structure. *)

Definition higher_supplied
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
    (V : X 4) (HV : is_horn_filler (SphereLowHomotopyHornN X b H) V)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopyOfFiller X b H V HV.

(** Only the single four-dimensional horn choice is assumed. *)

Definition higher_chosen
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopy X b H.

(** Descent uses the same actual conversion and generated relation. *)

Definition higher_class
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_low_homotopy_class X b H.

(** Endpoint respectfulness does not require any selected filler. *)

Definition higher_endpoints
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x x' y y' : TwoSphereS X b) (E : x ≈S x') (F : y ≈S y')
  : TwoSphereLowHomotopy X b x y ↔ TwoSphereLowHomotopy X b x' y'
  := TwoSphereLowHomotopy_proper X b x x' E y y' F.

End StrictSizes.
