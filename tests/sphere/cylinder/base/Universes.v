From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderBase.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_change_base_resp.

(** * Independent Native and Common Lift Bounds

    Retain both strict native orders, both strict final lift orders and
    the weakest complete interfaces, without enabling any algebra model. *)

(** ** Lower Equality Bound

    Fix one simplicial object, three vertices and three independent
    presentations. The two supplied vertex equalities retain their witnesses. *)

Section Lower.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).
Context (b c d : X 0) (E : b ≈S c) (F : c ≈S d).
Context (KR KR' KR'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC KC' KC'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The map needs only presentation choices and specified equality. *)

Definition lower_map
  : TwoSphereCylinderS X b KR KC →r TwoSphereCylinderS X c KR' KC'
  := two_sphere_cylinder_change_base_resp X KR KC KR' KC' E.

(** Retain each full coherence interface at these strict native bounds. *)

Definition lower_identity
  := two_sphere_cylinder_change_base_id X KR KC b.

Definition lower_witness
  := two_sphere_cylinder_change_base_witness X KR KC KR' KC' E E.

Definition lower_composition
  := two_sphere_cylinder_change_base_comp X KR KC KR' KC' KR'' KC'' E F.

Definition lower_unit
  := two_sphere_cylinder_change_base_unit X KR KC KR' KC' E.

(** Product comparison adds only four-dimensional missing-face-two choice. *)

Definition lower_minimal_product
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS X b)
  := two_sphere_cylinder_change_base_mul X KR KC KR' KC' E H K x y.

(** Only the source left choice and the target group choices are supplied. *)

Definition lower_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS X b)
  := two_sphere_cylinder_change_base_left_inverse X KR KC KR' KC'
      E I H K L x.

(** Common upward lifts retain either independent final size order. *)

Definition lower_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

Definition lower_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

(** Neither algebra nor full Kan nor raw cylinder equivalence is selected. *)

Fail Definition lower_no_group : HasMagma (TwoSphereCylinderS X b KR KC)
  := ltac:(typeclasses eauto).
Fail Definition lower_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition lower_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X c)
  := ltac:(typeclasses eauto).

End Lower.

(** ** Higher Equality Bound

    Fix one simplicial object, three vertices and three independent
    presentations. The two supplied vertex equalities retain their witnesses. *)

Section Higher.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (b c d : X 0) (E : b ≈S c) (F : c ≈S d).
Context (KR KR' KR'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC KC' KC'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The map needs only presentation choices and specified equality. *)

Definition higher_map
  : TwoSphereCylinderS X b KR KC →r TwoSphereCylinderS X c KR' KC'
  := two_sphere_cylinder_change_base_resp X KR KC KR' KC' E.

(** Retain each full coherence interface at these strict native bounds. *)

Definition higher_identity
  := two_sphere_cylinder_change_base_id X KR KC b.

Definition higher_witness
  := two_sphere_cylinder_change_base_witness X KR KC KR' KC' E E.

Definition higher_composition
  := two_sphere_cylinder_change_base_comp X KR KC KR' KC' KR'' KC'' E F.

Definition higher_unit
  := two_sphere_cylinder_change_base_unit X KR KC KR' KC' E.

(** Product comparison adds only four-dimensional missing-face-two choice. *)

Definition higher_minimal_product
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS X b)
  := two_sphere_cylinder_change_base_mul X KR KC KR' KC' E H K x y.

(** Only the source left choice and the target group choices are supplied. *)

Definition higher_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS X b)
  := two_sphere_cylinder_change_base_left_inverse X KR KC KR' KC'
      E I H K L x.

(** Common upward lifts retain either independent final size order. *)

Definition higher_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

Definition higher_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

(** Neither algebra nor full Kan nor raw cylinder equivalence is selected. *)

Fail Definition higher_no_group : HasMagma (TwoSphereCylinderS X b KR KC)
  := ltac:(typeclasses eauto).
Fail Definition higher_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition higher_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X c)
  := ltac:(typeclasses eauto).

End Higher.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_change_base_resp.
