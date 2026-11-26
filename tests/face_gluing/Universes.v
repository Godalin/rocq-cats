From Cats Require Import
  Instance.Set.Simplicial.FaceGluing.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Value, Equality and Membership Sizes

    Matching witnesses may be larger than both value universes. None of
    the gluing operations below requires a Kan selection. *)

Section StrictSizes.
Universes l u p r.
Constraint l < u, u < p, p < r.

(** Lower equality, with large Type-valued membership. *)

Definition lower_matching
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (n : nat)
    (P : Ordinal (S (S n)) → Type@{r})
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k, P j → P k → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
  : @SieveMatchingS Δ (S (S n)) (∃ j, P j)
      (λ _, S n) (λ j, δ[S n; j.1]) X
  := CofaceFacesMatching X n P a H.

(** Higher equality with the same independent membership size. *)

Definition higher_matching
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
    (P : Ordinal (S (S n)) → Type@{r})
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k, P j → P k → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
  : @SieveMatchingS Δ (S (S n)) (∃ j, P j)
      (λ _, S n) (λ j, δ[S n; j.1]) X
  := CofaceFacesMatching X n P a H.

(** Actual horns at both equality levels. *)

Definition lower_horn
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (n : nat)
    (i : Ordinal (S (S n))) (z : X (S (S n)))
  : HornS X (S (S n)) i
  := HornFacesN X n i (λ j, d[X; S n; j] z)
      (λ j k _ _ E, simplex_faces_pairwise X z j k E).

Definition higher_horn
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
    (i : Ordinal (S (S n))) (z : X (S (S n)))
  : HornS X (S (S n)) i
  := HornFacesN X n i (λ j, d[X; S n; j] z)
      (λ j k _ _ E, simplex_faces_pairwise X z j k E).

(** The supplied simplex really fills each whole descended horn. *)

Definition lower_filler
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (n : nat)
    (i : Ordinal (S (S n))) (z : X (S (S n)))
  : is_horn_filler (lower_horn X n i z) z
  := symmetry (horn_faces_of_simplex X n i z).

Definition higher_filler
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
    (i : Ordinal (S (S n))) (z : X (S (S n)))
  : is_horn_filler (higher_horn X n i z) z
  := symmetry (horn_faces_of_simplex X n i z).

(** Boundary gluing retains its actual restriction equations at both sizes. *)

Definition lower_boundary
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (n : nat)
    (z : X (S (S n)))
  : BoundaryFacesN X n (λ j, d[X; S n; j] z)
      (simplex_faces_pairwise X z) ≈S z↾∂[X; S (S n)]
  := boundary_faces_of_simplex X n z.

Definition higher_boundary
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
    (z : X (S (S n)))
  : BoundaryFacesN X n (λ j, d[X; S n; j] z)
      (simplex_faces_pairwise X z) ≈S z↾∂[X; S (S n)]
  := boundary_faces_of_simplex X n z.

End StrictSizes.
