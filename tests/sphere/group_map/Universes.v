From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereGroupMap.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Minimal Choices at Strict Sizes

    Test every public law with simplex equality strictly below and above
    its carrier. Product naturality needs only the target comparison;
    inverse naturality needs no source multiplication or source group. *)

(** ** Two Independent Equality Profiles

    Fix three strictly increasing levels; all choices below are explicit
    and no full Kan instance is present. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Only the target has a four-dimensional comparison choice. *)

Definition lower_map_mul
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (α : X ⇒ Y) (b : X 0)
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺)
    (x y : TwoSphereClassS X b)
  : two_sphere_class_map_resp α b (two_sphere_kan_mul X b H x y) ≈S
      two_sphere_kan_mul Y (α 0 b) K
        (two_sphere_class_map_resp α b x)
        (two_sphere_class_map_resp α b y)
  := two_sphere_class_map_mul α b H K x y.

(** No choices are needed to transport the constant unit. *)

Definition lower_base_unit
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b c : X 0) (E : b ≈S c)
  : two_sphere_class_change_base_resp X E (two_sphere_base X b) ≈S
      two_sphere_base X c
  := two_sphere_class_change_base_unit X E.

(** Equal-base products do not require descent choices three/four. *)

Definition lower_base_mul
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b c : X 0) (E : b ≈S c)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    (x y : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp X E
      (two_sphere_kan_mul X b H x y) ≈S
      two_sphere_kan_mul X c K (two_sphere_class_change_base_resp X E x)
        (two_sphere_class_change_base_resp X E y)
  := two_sphere_class_change_base_mul X E H K x y.

(** An arbitrary actual inverse tetrahedron suffices. *)

Definition lower_given_inverse
    (Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (c : Y 0)
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}
    `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺)
    (x y : TwoSphereS Y c)
    (W : TwoSphereComposite Y c y x (two_sphere_base Y c))
  : (y : TwoSphereClassS Y c) ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup Y c H K L)) x
  := two_sphere_composite_group_inverse Y c H K L W.

(** Only the source left-candidate choice enters inverse mapping. *)

Definition lower_map_inverse
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (α : X ⇒ Y) (b : X 0)
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}
    `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : two_sphere_class_map_resp α b (@SphereKanLeftInverse X b I x).1 ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup Y (α 0 b) H K L))
        (two_sphere_class_map_resp α b x)
  := two_sphere_class_map_left_inverse α b I H K L x.

(** The source candidate can be independent of both target candidates. *)

Definition lower_base_inverse
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b c : X 0) (E : b ≈S c)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp X E
      (@SphereKanLeftInverse X b I x).1 ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup X c H K L))
        (two_sphere_class_change_base_resp X E x)
  := two_sphere_class_change_base_left_inverse X E I H K L x.

(** The existing corrected inverse only needs comparison in its target X. *)

Definition lower_iso_inverse_mul
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (α : X ⇒ Y) (A : α ⦂ X ≅N Y)
    (b : X 0) `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺)
    (x y : TwoSphereClassS Y (α 0 b))
  : two_sphere_class_inverse_resp α A b
      (two_sphere_kan_mul Y (α 0 b) H x y) ≈S
      two_sphere_kan_mul X b K (two_sphere_class_inverse_resp α A b x)
        (two_sphere_class_inverse_resp α A b y)
  := two_sphere_class_inverse_mul α A b H K x y.

(** Only the target has a four-dimensional comparison choice. *)

Definition higher_map_mul
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (α : X ⇒ Y) (b : X 0)
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺)
    (x y : TwoSphereClassS X b)
  : two_sphere_class_map_resp α b (two_sphere_kan_mul X b H x y) ≈S
      two_sphere_kan_mul Y (α 0 b) K
        (two_sphere_class_map_resp α b x)
        (two_sphere_class_map_resp α b y)
  := two_sphere_class_map_mul α b H K x y.

(** No choices are needed to transport the constant unit. *)

Definition higher_base_unit
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b c : X 0) (E : b ≈S c)
  : two_sphere_class_change_base_resp X E (two_sphere_base X b) ≈S
      two_sphere_base X c
  := two_sphere_class_change_base_unit X E.

(** Equal-base products do not require descent choices three/four. *)

Definition higher_base_mul
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b c : X 0) (E : b ≈S c)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    (x y : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp X E
      (two_sphere_kan_mul X b H x y) ≈S
      two_sphere_kan_mul X c K (two_sphere_class_change_base_resp X E x)
        (two_sphere_class_change_base_resp X E y)
  := two_sphere_class_change_base_mul X E H K x y.

(** An arbitrary actual inverse tetrahedron suffices. *)

Definition higher_given_inverse
    (Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (c : Y 0)
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}
    `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺)
    (x y : TwoSphereS Y c)
    (W : TwoSphereComposite Y c y x (two_sphere_base Y c))
  : (y : TwoSphereClassS Y c) ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup Y c H K L)) x
  := two_sphere_composite_group_inverse Y c H K L W.

(** Only the source left-candidate choice enters inverse mapping. *)

Definition higher_map_inverse
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (α : X ⇒ Y) (b : X 0)
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}
    `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : two_sphere_class_map_resp α b (@SphereKanLeftInverse X b I x).1 ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup Y (α 0 b) H K L))
        (two_sphere_class_map_resp α b x)
  := two_sphere_class_map_left_inverse α b I H K L x.

(** The source candidate can be independent of both target candidates. *)

Definition higher_base_inverse
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b c : X 0) (E : b ≈S c)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp X E
      (@SphereKanLeftInverse X b I x).1 ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup X c H K L))
        (two_sphere_class_change_base_resp X E x)
  := two_sphere_class_change_base_left_inverse X E I H K L x.

(** The existing corrected inverse only needs comparison in its target X. *)

Definition higher_iso_inverse_mul
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (α : X ⇒ Y) (A : α ⦂ X ≅N Y)
    (b : X 0) `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺)
    (x y : TwoSphereClassS Y (α 0 b))
  : two_sphere_class_inverse_resp α A b
      (two_sphere_kan_mul Y (α 0 b) H x y) ≈S
      two_sphere_kan_mul X b K (two_sphere_class_inverse_resp α A b x)
        (two_sphere_class_inverse_resp α A b y)
  := two_sphere_class_inverse_mul α A b H K x y.

End StrictSizes.
