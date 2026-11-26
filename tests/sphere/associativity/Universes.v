From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereAssociativity.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and Minimal Associativity Choices

    A supplied actual filler needs no choice. Rebracketing selects only
    dimension-four missing face three; class comparison adds only missing
    face two. Multiplication choices remain independent explicit data. *)

(** ** Strict Levels

    Fix strictly increasing levels, probing simplex equality both below
    and above the carrier. The laws must retain those independent sizes. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Read a supplied filler without any chosen structure. *)

Definition lower_given
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (V : X 4) (HV : is_horn_filler (SphereAssociativityHornN X b A B C) V)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociateOfFiller X b A B C V HV.

(** Rebracketing needs only missing-face-three four-horns. *)

Definition lower_rebracket
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociate X b A B C.

(** Compare arbitrary supplied composites without a three-horn selection. *)

Definition lower_comparison
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (r : TwoSphereS X b) (D : TwoSphereComposite X b x t r)
  : (l : TwoSphereClassS X b) ≈S r
  := two_sphere_composite_assoc X b A B C D.

(** The selected associativity law uses no missing-face-four selection. *)

Definition lower_selected
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_kan_mul X b H x y) z ≈S
      two_sphere_kan_mul X b H x (two_sphere_kan_mul X b H y z)
  := two_sphere_kan_mul_assoc X b H x y z.

(** Four independent multiplication choices are covered by the supplied
    composite theorem, without identifying their choices or witnesses. *)

Definition lower_independent
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H1 H2 H3 H4 : HasHornFillers X 3 fin_first⁺⁺)
    (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H3 (two_sphere_kan_mul X b H1 x y) z ≈S
      two_sphere_kan_mul X b H4 x (two_sphere_kan_mul X b H2 y z).
Proof.
  exact (two_sphere_composite_assoc X b
    (TwoSphereKanMulComposite X b H1 x y)
    (TwoSphereKanMulComposite X b H2 y z)
    (TwoSphereKanMulComposite X b H3 (two_sphere_kan_mul X b H1 x y) z)
    (TwoSphereKanMulComposite X b H4 x (two_sphere_kan_mul X b H2 y z))).
Defined.

(** Read a supplied filler without any chosen structure. *)

Definition higher_given
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (V : X 4) (HV : is_horn_filler (SphereAssociativityHornN X b A B C) V)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociateOfFiller X b A B C V HV.

(** Rebracketing needs only missing-face-three four-horns. *)

Definition higher_rebracket
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociate X b A B C.

(** Compare arbitrary supplied composites without a three-horn selection. *)

Definition higher_comparison
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (r : TwoSphereS X b) (D : TwoSphereComposite X b x t r)
  : (l : TwoSphereClassS X b) ≈S r
  := two_sphere_composite_assoc X b A B C D.

(** The selected associativity law uses no missing-face-four selection. *)

Definition higher_selected
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_kan_mul X b H x y) z ≈S
      two_sphere_kan_mul X b H x (two_sphere_kan_mul X b H y z)
  := two_sphere_kan_mul_assoc X b H x y z.

(** Four independent multiplication choices are covered by the supplied
    composite theorem, without identifying their choices or witnesses. *)

Definition higher_independent
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H1 H2 H3 H4 : HasHornFillers X 3 fin_first⁺⁺)
    (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H3 (two_sphere_kan_mul X b H1 x y) z ≈S
      two_sphere_kan_mul X b H4 x (two_sphere_kan_mul X b H2 y z).
Proof.
  exact (two_sphere_composite_assoc X b
    (TwoSphereKanMulComposite X b H1 x y)
    (TwoSphereKanMulComposite X b H2 y z)
    (TwoSphereKanMulComposite X b H3 (two_sphere_kan_mul X b H1 x y) z)
    (TwoSphereKanMulComposite X b H4 x (two_sphere_kan_mul X b H2 y z))).
Defined.

End StrictSizes.
