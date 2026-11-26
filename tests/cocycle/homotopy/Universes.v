From Cats Require Import
  Instance.Bool.CocycleHomotopy.

From Cats Require Import
  Cat.Groupoid.Core.

Import Cats.Instance.Set.Groupoid (EqGpd).
Import Cats.Instance.Set.Simplicial.Vertex.Core (VtxNerve).

Local Open Scope nat_scope.

(** * Map Invariants at Independent Sizes

    Probe opposite strict coefficient profiles and both ambient equality
    orders. The generated map witnesses are not forced into either native
    coefficient equality or the original simplex equality bound. *)

Section CoefficientSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : Monoid@{h e _}) (N : Monoid@{e h _}).

(** The lower native / lower ambient evaluation
    retains the whole generated map relation. *)

Definition lower_native_lower_ambient_evaluation
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS M X →r M
  := cocycle_homotopy_evaluation_resp b x.

(** The lower native / higher ambient evaluation
    retains the whole generated map relation. *)

Definition lower_native_higher_ambient_evaluation
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS M X →r M
  := cocycle_homotopy_evaluation_resp b x.

(** The higher native / lower ambient evaluation
    retains the whole generated map relation. *)

Definition higher_native_lower_ambient_evaluation
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS N X →r N
  := cocycle_homotopy_evaluation_resp b x.

(** The higher native / higher ambient evaluation
    retains the whole generated map relation. *)

Definition higher_native_higher_ambient_evaluation
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS N X →r N
  := cocycle_homotopy_evaluation_resp b x.

End CoefficientSizes.

(** ** Explicit Edge Reduction without a Model

    These probes use arbitrary targets and an explicit edge law, without
    coefficient structures or Kan choices. *)

Section GenericSizes.
Universes l u p.
Constraint l < u, u < p.

(** The lower ambient equality admits the actual restricted cylinder. *)

Definition lower_equality_restricted_cylinder
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (c : Y 0)
    (E1 : ∀ z : Y 1, z ≈S simplex_constant Y c 1)
    (f g : X ⇒ Y) (H : SimplicialHomotopy f g)
    (b : X 0) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (one_reduced_sphere_resp Y c E1 (f 2 x.1))
      (one_reduced_sphere_resp Y c E1 (g 2 x.1))
  := OneReducedSphereCylinder Y c E1 H b x.

(** The higher ambient equality admits the actual restricted cylinder. *)

Definition higher_equality_restricted_cylinder
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (c : Y 0)
    (E1 : ∀ z : Y 1, z ≈S simplex_constant Y c 1)
    (f g : X ⇒ Y) (H : SimplicialHomotopy f g)
    (b : X 0) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (one_reduced_sphere_resp Y c E1 (f 2 x.1))
      (one_reduced_sphere_resp Y c E1 (g 2 x.1))
  := OneReducedSphereCylinder Y c E1 H b x.

End GenericSizes.

(** ** A Category with Unequal Native Hom Sizes

    Ordinary category Hom equality remains smaller than its carrier;
    both ambient equality orders retain the stronger map obstruction. *)

Section NerveSizes.
Universes e h o l u p.
Constraint e < h, h < o, o < l, l < u, u < p.
Context (A : SetC@{o e}) (C : Cat@{o h e l l})
    (T : Fct (EqGpd A) C).

(** The lower ambient equality admits the obstruction for arbitrary maps. *)

Definition lower_equality_nerve_obstruction
    (f : (Z²(BoolS_Monoid) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒
      (VtxNerve T : Fct (Δ^op) SetCat@{u o _ _ _ _ _}))
    (g : VtxNerve T ⇒ Z²(BoolS_Monoid))
  : ¬ SimplicialHomotopy (g ∘Nv f) IdN
  := bool_cocycle_no_nerve_forward_homotopy T f g.

(** The higher ambient equality admits the obstruction for arbitrary maps. *)

Definition higher_equality_nerve_obstruction
    (f : (Z²(BoolS_Monoid) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      (VtxNerve T : Fct (Δ^op) SetCat@{u p _ _ _ _ _}))
    (g : VtxNerve T ⇒ Z²(BoolS_Monoid))
  : ¬ SimplicialHomotopy (g ∘Nv f) IdN
  := bool_cocycle_no_nerve_forward_homotopy T f g.

End NerveSizes.
