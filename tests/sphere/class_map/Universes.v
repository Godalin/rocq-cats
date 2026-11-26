From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMap.

Local Open Scope nat_scope.

(** * Independent Sizes for Generic Sphere-Class Maps

    Generated class witnesses may exceed simplex equality. All lifted
    comparisons use genuine upward bounds, in either strict order for
    their final carrier and equality sizes. *)

Section IndependentSizes.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.

(** Natural isomorphism at lower ambient and higher final equality. *)

Definition lower_ambient_higher_common_iso
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Natural isomorphism at lower ambient and lower final equality. *)

Definition lower_ambient_lower_common_iso
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ q v} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ q v} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Equality transport at lower ambient equality. *)

Definition lower_ambient_base_iso
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (b c : X 0) (E : b ≈S c)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS X c)
  := two_sphere_class_change_base_iso X E.

(** Actual composition witnesses at lower ambient equality. *)

Definition lower_ambient_composite_map
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (α : X ⇒ Y) (b : X 0) (x y z : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite Y (α 0 b)
      (two_sphere_map_resp α b x) (two_sphere_map_resp α b y)
      (two_sphere_map_resp α b z)
  := two_sphere_composite_map α b H.

(** Natural isomorphism at higher ambient and higher final equality. *)

Definition higher_ambient_higher_common_iso
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Natural isomorphism at higher ambient and lower final equality. *)

Definition higher_ambient_lower_common_iso
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ q v} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ q v} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Equality transport at higher ambient equality. *)

Definition higher_ambient_base_iso
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (b c : X 0) (E : b ≈S c)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS X c)
  := two_sphere_class_change_base_iso X E.

(** Actual composition witnesses at higher ambient equality. *)

Definition higher_ambient_composite_map
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (α : X ⇒ Y) (b : X 0) (x y z : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite Y (α 0 b)
      (two_sphere_map_resp α b x) (two_sphere_map_resp α b y)
      (two_sphere_map_resp α b z)
  := two_sphere_composite_map α b H.

End IndependentSizes.
