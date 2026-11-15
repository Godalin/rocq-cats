From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderSetoid.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereCylinderEquivalence TwoSphereClassCylinder
  two_sphere_cylinder_class_iff two_sphere_cylinder_map_natural
  two_sphere_cylinder_map_resp.

(** * Independent Native and Common Bounds

    Both native carrier/equality orders are strict. Each comparison is also
    tested with either strict order of its final upward lift bounds. *)

(** * 独立原生界与共同界

    两种原生载体／相等次序均严格，并对每种比较检查最终向上提升界的两种严格次序。 *)

(** ** Lower Native Equality

    Fix unrelated representative/equality sizes and independently supplied
    presentation choices; no full Kan or selected algebra is available. *)

(** ** 较小原生相等

    固定独立代表／相等大小及各自给定的呈现选择，不提供完整Kan或选定代数。 *)

Section Lower.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (α : X ⇒ Y) (b : X 0).
Context (KR KR' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC KC' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (LR : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (LC : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

Definition lower_carrier_is_original
  : carrier (TwoSphereCylinderS X b KR KC) = TwoSphereS X b
  := eq_refl.

Definition lower_equality_is_original (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : (x : TwoSphereCylinderS X b KR KC) ≈S y
  := H.

Definition lower_forward
  : TwoSphereClassS X b →r TwoSphereCylinderS X b KR KC
  := two_sphere_cylinder_of_class_resp X b KR KC.

Definition lower_backward
  : TwoSphereCylinderS X b KR KC →r TwoSphereClassS X b
  := two_sphere_class_of_cylinder_resp X b KR KC.

Definition lower_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
  := two_sphere_cylinder_class_iso X b KR KC.

Definition lower_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereClassS X b) ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC)
  := two_sphere_cylinder_class_iso X b KR KC.

Definition lower_higher_final_choice
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC) ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X b KR' KC')
  := two_sphere_cylinder_choice_iso X b KR KC KR' KC'.

Definition lower_lower_final_choice
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC) ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X b KR' KC')
  := two_sphere_cylinder_choice_iso X b KR KC KR' KC'.

Definition lower_map
  : TwoSphereCylinderS X b KR KC →r TwoSphereCylinderS Y (α 0 b) LR LC
  := two_sphere_cylinder_map_resp α b KR KC LR LC.

(** Retain the whole pointwise naturality interface at these strict sizes. *)

(** 在这些严格大小处保留完整的逐点自然性接口。 *)

Definition lower_natural
  := two_sphere_cylinder_map_natural α b KR KC LR LC.

(** The naturality component is an actual cylinder on the image triangle. *)

(** 自然性分量是像三角形上的实际柱。 *)

Local Transparent two_sphere_cylinder_map_resp.

Definition lower_natural_value (x : TwoSphereClassS X b)
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_map_resp α b x) (two_sphere_map_resp α b x)
  := two_sphere_cylinder_map_natural α b KR KC LR LC x.

Local Opaque two_sphere_cylinder_map_resp.

Definition lower_map_cylinder (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : (two_sphere_cylinder_map_resp α b KR KC LR LC x
      : TwoSphereCylinderS Y (α 0 b) LR LC) ≈S
      two_sphere_cylinder_map_resp α b KR KC LR LC y
  := @func_proper _ _ lower_map x y H.

Fail Definition lower_no_automatic_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := ltac:(typeclasses eauto).

Fail Definition lower_no_automatic_Kan
  : HasKanFillers X
  := ltac:(typeclasses eauto).

End Lower.

(** ** Higher Native Equality

    Fix unrelated representative/equality sizes and independently supplied
    presentation choices; no full Kan or selected algebra is available. *)

(** ** 较大原生相等

    固定独立代表／相等大小及各自给定的呈现选择，不提供完整Kan或选定代数。 *)

Section Higher.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (α : X ⇒ Y) (b : X 0).
Context (KR KR' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC KC' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (LR : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (LC : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

Definition higher_carrier_is_original
  : carrier (TwoSphereCylinderS X b KR KC) = TwoSphereS X b
  := eq_refl.

Definition higher_equality_is_original (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : (x : TwoSphereCylinderS X b KR KC) ≈S y
  := H.

Definition higher_forward
  : TwoSphereClassS X b →r TwoSphereCylinderS X b KR KC
  := two_sphere_cylinder_of_class_resp X b KR KC.

Definition higher_backward
  : TwoSphereCylinderS X b KR KC →r TwoSphereClassS X b
  := two_sphere_class_of_cylinder_resp X b KR KC.

Definition higher_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
  := two_sphere_cylinder_class_iso X b KR KC.

Definition higher_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereClassS X b) ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC)
  := two_sphere_cylinder_class_iso X b KR KC.

Definition higher_higher_final_choice
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC) ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X b KR' KC')
  := two_sphere_cylinder_choice_iso X b KR KC KR' KC'.

Definition higher_lower_final_choice
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC) ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X b KR' KC')
  := two_sphere_cylinder_choice_iso X b KR KC KR' KC'.

Definition higher_map
  : TwoSphereCylinderS X b KR KC →r TwoSphereCylinderS Y (α 0 b) LR LC
  := two_sphere_cylinder_map_resp α b KR KC LR LC.

(** Retain the whole pointwise naturality interface at these strict sizes. *)

(** 在这些严格大小处保留完整的逐点自然性接口。 *)

Definition higher_natural
  := two_sphere_cylinder_map_natural α b KR KC LR LC.

(** The naturality component is an actual cylinder on the image triangle. *)

(** 自然性分量是像三角形上的实际柱。 *)

Local Transparent two_sphere_cylinder_map_resp.

Definition higher_natural_value (x : TwoSphereClassS X b)
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_map_resp α b x) (two_sphere_map_resp α b x)
  := two_sphere_cylinder_map_natural α b KR KC LR LC x.

Local Opaque two_sphere_cylinder_map_resp.

Definition higher_map_cylinder (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : (two_sphere_cylinder_map_resp α b KR KC LR LC x
      : TwoSphereCylinderS Y (α 0 b) LR LC) ≈S
      two_sphere_cylinder_map_resp α b KR KC LR LC y
  := @func_proper _ _ higher_map x y H.

Fail Definition higher_no_automatic_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := ltac:(typeclasses eauto).

Fail Definition higher_no_automatic_Kan
  : HasKanFillers X
  := ltac:(typeclasses eauto).

End Higher.


Local Transparent TwoSphereCylinderEquivalence TwoSphereClassCylinder
  two_sphere_cylinder_class_iff two_sphere_cylinder_map_natural
  two_sphere_cylinder_map_resp.
