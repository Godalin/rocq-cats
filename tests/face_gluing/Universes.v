From Cats Require Import
  Instance.Set.Simplicial.FaceGluing.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Value, Equality and Membership Sizes

    Matching witnesses may be larger than both value universes. None of
    the gluing operations below requires a Kan selection. *)

(** * 独立的值、相等与成员大小

    匹配成员见证可以大于值的两个宇宙；下列粘合均不要求 Kan 选择。 *)

Section StrictSizes.
Universes l u p r.
Constraint l < u, u < p, p < r.

(** Lower equality, with large Type-valued membership. *)

(** 较低相等层级与较大的 Type 值成员关系。 *)

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

(** 较高相等层级与相同的独立成员大小。 *)

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

(** 两种相等层级下的实际 horn。 *)

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

(** 给定单形确实填充每个完整的下降 horn。 *)

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

(** 两种大小下的边界粘合均保留实际限制方程。 *)

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
