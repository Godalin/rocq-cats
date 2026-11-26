From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderComparison.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereCylinderEquivalence TwoSphereElementaryForwardCylinder
  TwoSphereClassCylinder two_sphere_cylinder_class_iff.

(** * Explicit Choices at Independent Sizes

    Test both strict carrier/equality orders. No complete Kan structure,
    multiplication or automatically selected cylinder equivalence is given. *)

(** ** Lower Equality Bounds

    Keep all choices explicit and check both directions, actual endpoints
    and a boundary restriction with independently supplied time. *)

Section Lower.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (x y : TwoSphereS X b).

Definition lower_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := TwoSphereCylinderEquivalence X b KR KC.

Definition lower_elementary (H : TwoSphereHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereElementaryForwardCylinder X b KR H.

Definition lower_fold (H : (x : TwoSphereClassS X b) ≈S y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereClassCylinder X b KR KC H.

Definition lower_boundary (H : (x : TwoSphereClassS X b) ≈S y)
    (n : nat) (a : (∂Δ[2]) n) (t : (Δ[1]) n)
  : homotopy_map (lower_fold H).1 n (ι∂[2] n a, t) ≈S
      simplex_constant X b n
  := (lower_fold H).2 n a t.

Definition lower_endpoint (H : (x : TwoSphereClassS X b) ≈S y)
  : (homotopy_map (lower_fold H).1 ∘Nv
      SimplicialEndpointN (Δ[2]) false) ≈N (@simplex_map_resp X 2 x.1)
  := simplicial_homotopy_0 (lower_fold H).1.

Definition lower_iff
  : TwoSphereCylinderHomotopy X b x y ↔
      (x : TwoSphereClassS X b) ≈S y
  := two_sphere_cylinder_class_iff X b KR KC x y.

Definition lower_recovered_class
    (H : (x : TwoSphereClassS X b) ≈S y)
  : (x : TwoSphereClassS X b) ≈S y
  := fst lower_iff (lower_fold H).

Fail Definition lower_no_automatic_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := ltac:(typeclasses eauto).

Fail Definition lower_no_automatic_full_Kan
  : HasKanFillers X
  := ltac:(typeclasses eauto).

End Lower.

(** ** Higher Equality Bounds

    Keep all choices explicit and check both directions, actual endpoints
    and a boundary restriction with independently supplied time. *)

Section Higher.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (x y : TwoSphereS X b).

Definition higher_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := TwoSphereCylinderEquivalence X b KR KC.

Definition higher_elementary (H : TwoSphereHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereElementaryForwardCylinder X b KR H.

Definition higher_fold (H : (x : TwoSphereClassS X b) ≈S y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereClassCylinder X b KR KC H.

Definition higher_boundary (H : (x : TwoSphereClassS X b) ≈S y)
    (n : nat) (a : (∂Δ[2]) n) (t : (Δ[1]) n)
  : homotopy_map (higher_fold H).1 n (ι∂[2] n a, t) ≈S
      simplex_constant X b n
  := (higher_fold H).2 n a t.

Definition higher_endpoint (H : (x : TwoSphereClassS X b) ≈S y)
  : (homotopy_map (higher_fold H).1 ∘Nv
      SimplicialEndpointN (Δ[2]) false) ≈N (@simplex_map_resp X 2 x.1)
  := simplicial_homotopy_0 (higher_fold H).1.

Definition higher_iff
  : TwoSphereCylinderHomotopy X b x y ↔
      (x : TwoSphereClassS X b) ≈S y
  := two_sphere_cylinder_class_iff X b KR KC x y.

Definition higher_recovered_class
    (H : (x : TwoSphereClassS X b) ≈S y)
  : (x : TwoSphereClassS X b) ≈S y
  := fst higher_iff (higher_fold H).

Fail Definition higher_no_automatic_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := ltac:(typeclasses eauto).

Fail Definition higher_no_automatic_full_Kan
  : HasKanFillers X
  := ltac:(typeclasses eauto).

End Higher.

(** ** Full Kan Still Requires Explicit Enabling

    A supplied full Kan witness can furnish the stated families, but it
    does not register the new cylinder equivalence automatically. *)

Section FullKanClient.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (HK : HasKanFillers X).
Local Existing Instance HK.

Definition full_Kan_comparison (x y : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X b x y ↔
      (x : TwoSphereClassS X b) ≈S y
  := two_sphere_cylinder_class_iff X b
      (λ s, @hasHornFillers X HK (simplex_triangle_horn_face_dim s)
        (simplex_triangle_horn_missing fin_first s))
      (λ s, @hasHornFillers X HK (simplex_triangle_horn_face_dim s)
        (simplex_triangle_horn_missing fin_first⁺ s)) x y.

Fail Definition full_Kan_does_not_automatically_enable_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := ltac:(typeclasses eauto).

End FullKanClient.

Local Transparent TwoSphereCylinderEquivalence TwoSphereElementaryForwardCylinder
  TwoSphereClassCylinder two_sphere_cylinder_class_iff.
