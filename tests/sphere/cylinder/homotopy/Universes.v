From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderHomotopy.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_homotopy_inverse_resp
  two_sphere_cylinder_map_resp.

(** * Independent Native and Common Lift Bounds

    Test the corrected inverse and its weakest complete interfaces at
    both native size orders and both common upward-lift orders. *)

(** ** Lower Equality Bound

    Fix actual composite homotopies and their independent constant trajectories.
    No selected algebra or full Kan structure is initially supplied. *)

Section Lower.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).
Context (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0).
Context (T : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X)).
Context (E : homotopy_map T 1 (simplex_constant X b 1, simplex_generic 1)
  ≈S simplex_constant X b 1).
Context (U : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y)).
Context (F : homotopy_map U 1
  (simplex_constant Y (f 0 b) 1, simplex_generic 1)
  ≈S simplex_constant Y (f 0 b) 1).
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
  : TwoSphereCylinderS Y (f 0 b) KRY KCY →r
      TwoSphereCylinderS X b KRX KCX
  := two_sphere_cylinder_homotopy_inverse_resp f g b T E KRX KCX KRY KCY.

(** Retain complete round-trip and unit interfaces without added algebra. *)

Definition lower_left
  := two_sphere_cylinder_homotopy_inverse_l f g b T E KRX KCX KRY KCY.

Definition lower_right
  := two_sphere_cylinder_homotopy_inverse_r f g b T E KRX KCX KRY KCY U F.

(** Reflection needs only the first homotopy and the existing KR entries. *)

Definition lower_reflection
  := two_sphere_cylinder_homotopy_reflect f g b T E KRX KCX KRY KCY.

Definition lower_unit
  := two_sphere_cylinder_homotopy_inverse_unit f g b T E KRX KCX KRY KCY.

(** Products reuse the existing KRX entry without an extra comparison choice. *)

Definition lower_minimal_product
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS Y (f 0 b))
  := two_sphere_cylinder_homotopy_inverse_mul f g b T E KRX KCX KRY KCY H K x y.

(** No Y product, right candidate or Group is used to map its left candidate. *)

Definition lower_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS Y (f 0 b))
  := two_sphere_cylinder_homotopy_inverse_left_inverse f g b T E
      KRX KCX KRY KCY I H K L x.

(** Both final size orders contain the original native equality witnesses. *)

Definition lower_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS Y (f 0 b) KRY KCY)
  := two_sphere_cylinder_homotopy_iso f g b T E KRX KCX KRY KCY U F.

Definition lower_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS Y (f 0 b) KRY KCY)
  := two_sphere_cylinder_homotopy_iso f g b T E KRX KCX KRY KCY U F.

(** The isomorphism does not select either Group or full Kan choices. *)

Fail Definition lower_no_X_group : HasMagma (TwoSphereCylinderS X b KRX KCX)
  := ltac:(typeclasses eauto).
Fail Definition lower_no_Y_group
  : HasMagma (TwoSphereCylinderS Y (f 0 b) KRY KCY)
  := ltac:(typeclasses eauto).
Fail Definition lower_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).

End Lower.

(** ** Higher Equality Bound

    Fix actual composite homotopies and their independent constant trajectories.
    No selected algebra or full Kan structure is initially supplied. *)

Section Higher.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0).
Context (T : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X)).
Context (E : homotopy_map T 1 (simplex_constant X b 1, simplex_generic 1)
  ≈S simplex_constant X b 1).
Context (U : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y)).
Context (F : homotopy_map U 1
  (simplex_constant Y (f 0 b) 1, simplex_generic 1)
  ≈S simplex_constant Y (f 0 b) 1).
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
  : TwoSphereCylinderS Y (f 0 b) KRY KCY →r
      TwoSphereCylinderS X b KRX KCX
  := two_sphere_cylinder_homotopy_inverse_resp f g b T E KRX KCX KRY KCY.

(** Retain complete round-trip and unit interfaces without added algebra. *)

Definition higher_left
  := two_sphere_cylinder_homotopy_inverse_l f g b T E KRX KCX KRY KCY.

Definition higher_right
  := two_sphere_cylinder_homotopy_inverse_r f g b T E KRX KCX KRY KCY U F.

(** Reflection needs only the first homotopy and the existing KR entries. *)

Definition higher_reflection
  := two_sphere_cylinder_homotopy_reflect f g b T E KRX KCX KRY KCY.

Definition higher_unit
  := two_sphere_cylinder_homotopy_inverse_unit f g b T E KRX KCX KRY KCY.

(** Products reuse the existing KRX entry without an extra comparison choice. *)

Definition higher_minimal_product
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS Y (f 0 b))
  := two_sphere_cylinder_homotopy_inverse_mul f g b T E KRX KCX KRY KCY H K x y.

(** No Y product, right candidate or Group is used to map its left candidate. *)

Definition higher_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS Y (f 0 b))
  := two_sphere_cylinder_homotopy_inverse_left_inverse f g b T E
      KRX KCX KRY KCY I H K L x.

(** Both final size orders contain the original native equality witnesses. *)

Definition higher_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS Y (f 0 b) KRY KCY)
  := two_sphere_cylinder_homotopy_iso f g b T E KRX KCX KRY KCY U F.

Definition higher_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS Y (f 0 b) KRY KCY)
  := two_sphere_cylinder_homotopy_iso f g b T E KRX KCX KRY KCY U F.

(** The isomorphism does not select either Group or full Kan choices. *)

Fail Definition higher_no_X_group : HasMagma (TwoSphereCylinderS X b KRX KCX)
  := ltac:(typeclasses eauto).
Fail Definition higher_no_Y_group
  : HasMagma (TwoSphereCylinderS Y (f 0 b) KRY KCY)
  := ltac:(typeclasses eauto).
Fail Definition higher_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).

End Higher.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_homotopy_inverse_resp
  two_sphere_cylinder_map_resp.
