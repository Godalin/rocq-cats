From Cats Require Import
  Instance.Set.Simplicial.Cocycle.SphereGroup.

(** * Group Constructions at Strictly Different Sizes

    The coefficient carrier and equality sizes remain independent, as do
    the ambient simplex sizes. The generated class witnesses may live at
    larger bounds; no resizing axiom or equality of bounds is required. *)

Section GroupSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : Group@{h e _}) (N : Group@{e h _}).

(** Lower native and lower ambient equality. *)

Definition lower_native_lower_ambient_group
  : ∃ G : Group, (G : SetC) =
      TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)
  := (cocycle_two_sphere_Group (M := M); eq_refl).

(** Lower native and higher ambient equality. *)

Definition lower_native_higher_ambient_group
  : ∃ G : Group, (G : SetC) =
      TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)
  := (cocycle_two_sphere_Group (M := M); eq_refl).

(** Higher native and lower ambient equality. *)

Definition higher_native_lower_ambient_group
  : ∃ G : Group, (G : SetC) =
      TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)
  := (cocycle_two_sphere_Group (M := N); eq_refl).

(** Higher native and higher ambient equality. *)

Definition higher_native_higher_ambient_group
  : ∃ G : Group, (G : SetC) =
      TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)
  := (cocycle_two_sphere_Group (M := N); eq_refl).

Context `{HC : !IsCommMagma M} `{HD : !IsCommMagma N}.

(** Commutativity keeps the same parent at lower ambient equality. *)

Definition lower_ambient_commutativity
  : @IsCommMagma (GroupToMonoid lower_native_lower_ambient_group.1)
      (Monoid_hasMagma (GroupToMonoid lower_native_lower_ambient_group.1))
  := cocycle_two_sphere_IsCommMagma.

(** The opposite native profile accepts higher ambient equality too. *)

Definition higher_ambient_commutativity
  : @IsCommMagma (GroupToMonoid higher_native_higher_ambient_group.1)
      (Monoid_hasMagma (GroupToMonoid higher_native_higher_ambient_group.1))
  := cocycle_two_sphere_IsCommMagma.

End GroupSizes.

(** ** Geometric Witnesses at Independent Sizes

    The actual tetrahedron and its sphere-class comparison must also
    accept the two opposite strict ambient equality profiles. *)

Section FillerSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : Monoid@{h e _}).

(** Lower ambient equality with retained simplex data. *)

Definition lower_ambient_composite
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereComposite _ _ x y (cocycle_two_sphere_mul x y)
  := CocycleTwoSphereMul x y.

(** Higher ambient equality with the same construction. *)

Definition higher_ambient_composite
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereComposite _ _ x y (cocycle_two_sphere_mul x y)
  := CocycleTwoSphereMul x y.

End FillerSizes.
