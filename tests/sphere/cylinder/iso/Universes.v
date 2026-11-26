From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderIso.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_inverse_resp
  two_sphere_cylinder_map_resp.

(** * Independent Native and Common Lift Bounds

    Test the corrected inverse and its weakest complete interfaces at
    both native size orders and both common upward-lift orders. *)

(** ** Lower Equality Bound

    Fix a natural isomorphism with independent explicit presentations.
    No selected algebra or full Kan structure is initially supplied. *)

Section Lower.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).
Context (α : X ⇒ Y) (A : α ⦂ X ≅N Y) (b : X 0).
Context (KRX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The inverse is respectful for actual-cylinder equality. *)

Definition lower_inverse
  : TwoSphereCylinderS Y (α 0 b) KRY KCY →r
      TwoSphereCylinderS X b KRX KCX
  := two_sphere_cylinder_inverse_resp α A b KRX KCX KRY KCY.

(** Retain complete round-trip and unit interfaces without added algebra. *)

Definition lower_left
  := two_sphere_cylinder_inverse_l α A b KRX KCX KRY KCY.

Definition lower_right
  := two_sphere_cylinder_inverse_r α A b KRX KCX KRY KCY.

Definition lower_unit
  := two_sphere_cylinder_inverse_unit α A b KRX KCX KRY KCY.

(** Only X missing-face-two comparison is required for products. *)

Definition lower_minimal_product
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS Y (α 0 b))
  := two_sphere_cylinder_inverse_mul α A b KRX KCX KRY KCY H K x y.

(** No Y product, right candidate or Group is used to map its left candidate. *)

Definition lower_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS Y (α 0 b))
  := two_sphere_cylinder_inverse_left_inverse α A b
      KRX KCX KRY KCY I H K L x.

(** Both final size orders contain the original native equality witnesses. *)

Definition lower_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS Y (α 0 b) KRY KCY)
  := two_sphere_cylinder_iso α A b KRX KCX KRY KCY.

Definition lower_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS Y (α 0 b) KRY KCY)
  := two_sphere_cylinder_iso α A b KRX KCX KRY KCY.

(** The isomorphism does not select either Group or full Kan choices. *)

Fail Definition lower_no_X_group : HasMagma (TwoSphereCylinderS X b KRX KCX)
  := ltac:(typeclasses eauto).
Fail Definition lower_no_Y_group
  : HasMagma (TwoSphereCylinderS Y (α 0 b) KRY KCY)
  := ltac:(typeclasses eauto).
Fail Definition lower_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).

End Lower.

(** ** Higher Equality Bound

    Fix a natural isomorphism with independent explicit presentations.
    No selected algebra or full Kan structure is initially supplied. *)

Section Higher.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (α : X ⇒ Y) (A : α ⦂ X ≅N Y) (b : X 0).
Context (KRX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The inverse is respectful for actual-cylinder equality. *)

Definition higher_inverse
  : TwoSphereCylinderS Y (α 0 b) KRY KCY →r
      TwoSphereCylinderS X b KRX KCX
  := two_sphere_cylinder_inverse_resp α A b KRX KCX KRY KCY.

(** Retain complete round-trip and unit interfaces without added algebra. *)

Definition higher_left
  := two_sphere_cylinder_inverse_l α A b KRX KCX KRY KCY.

Definition higher_right
  := two_sphere_cylinder_inverse_r α A b KRX KCX KRY KCY.

Definition higher_unit
  := two_sphere_cylinder_inverse_unit α A b KRX KCX KRY KCY.

(** Only X missing-face-two comparison is required for products. *)

Definition higher_minimal_product
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS Y (α 0 b))
  := two_sphere_cylinder_inverse_mul α A b KRX KCX KRY KCY H K x y.

(** No Y product, right candidate or Group is used to map its left candidate. *)

Definition higher_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS Y (α 0 b))
  := two_sphere_cylinder_inverse_left_inverse α A b
      KRX KCX KRY KCY I H K L x.

(** Both final size orders contain the original native equality witnesses. *)

Definition higher_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS Y (α 0 b) KRY KCY)
  := two_sphere_cylinder_iso α A b KRX KCX KRY KCY.

Definition higher_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS Y (α 0 b) KRY KCY)
  := two_sphere_cylinder_iso α A b KRX KCX KRY KCY.

(** The isomorphism does not select either Group or full Kan choices. *)

Fail Definition higher_no_X_group : HasMagma (TwoSphereCylinderS X b KRX KCX)
  := ltac:(typeclasses eauto).
Fail Definition higher_no_Y_group
  : HasMagma (TwoSphereCylinderS Y (α 0 b) KRY KCY)
  := ltac:(typeclasses eauto).
Fail Definition higher_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).

End Higher.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_inverse_resp
  two_sphere_cylinder_map_resp.
