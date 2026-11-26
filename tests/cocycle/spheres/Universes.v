From Cats Require Import
  Instance.Bool.CocycleSphere.
From Cats Require
  Instance.Set.Simplicial.Vertex.Core.

From Cats Require Import
  Cat.Groupoid.Core.

Import Cats.Instance.Set.Groupoid (EqGpd).
Import Cats.Instance.Set.Simplicial.Vertex.Core (VtxNerve).

(** * Sphere Classes at Strictly Different Sizes

    The retained boundary and homotopy witnesses may enlarge the class
    setoid. Its original ambient simplex sizes remain independent, as do
    the coefficient carrier/equality sizes and the final common lifts. *)

Section CoefficientSizes.
Universes e h l u p v q.
Constraint e < h, h < l, l < u, u < p, p < v, v < q.
Context (M : Monoid@{h e _}) (N : Monoid@{e h _}).

(** Lower native equality and lower ambient equality. *)

Definition lower_native_lower_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} M
  := cocycle_two_sphere_class_iso.

(** Lower native equality and higher ambient equality. *)

Definition lower_native_higher_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} M
  := cocycle_two_sphere_class_iso.

(** Higher native equality and lower ambient equality. *)

Definition higher_native_lower_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} N
  := cocycle_two_sphere_class_iso.

(** Higher native equality and higher ambient equality. *)

Definition higher_native_higher_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} N
  := cocycle_two_sphere_class_iso.

(** The final common equality bound may lie below its carrier bound. *)

Definition lower_common_equality_class_iso
  : LiftS@{_ _ q v}
      (TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ q v} M
  := cocycle_two_sphere_class_iso.

(** The opposite native profile retains the same independent common lifts. *)

Definition reverse_lower_common_equality_class_iso
  : LiftS@{_ _ q v}
      (TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ q v} N
  := cocycle_two_sphere_class_iso.

End CoefficientSizes.

(** ** Ordinary Categories with Independent Native Hom Sizes

    The obstruction does not force hom equality to the hom carrier size,
    and works at both strict ambient equality orders. *)

Section NerveSizes.
Universes e h o l u p.
Constraint e < h, h < o, o < l, l < u, u < p.
Context (A : SetC@{o e}) (C : Cat@{o h e l l})
    (T : Fct (EqGpd A) C).

(** Lower ambient equality retains the obstruction. *)

Definition lower_equality_nerve_obstruction
  : ¬ ((Z²(BoolS_Monoid) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ≅N
      (VtxNerve T : Fct (Δ^op) SetCat@{u o _ _ _ _ _}))
  := bool_cocycle_not_vertex_nerve T.

(** Higher ambient equality retains the same obstruction. *)

Definition higher_equality_nerve_obstruction
  : ¬ ((Z²(BoolS_Monoid) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      (VtxNerve T : Fct (Δ^op) SetCat@{u p _ _ _ _ _}))
  := bool_cocycle_not_vertex_nerve T.

End NerveSizes.
