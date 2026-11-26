From Cats Require Import
  Instance.Set.Simplicial.Prism
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Bool.CocycleSphere.
From Cats.Set Require Import
  OrdinalMaximum.
From Cats Require Import
  Cat.Core
  Cat.Diagram.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Staircases and Degenerate Inputs

    Compute the selected pivot and the whole factor, rather than merely
    count the three top-dimensional pieces. Restriction may change the
    pivot, while the same interleaving formula remains natural. *)

Definition staircase_factor (i : Ordinal 2)
  := SimplexPrismFactor σ[2; i] (two_sphere_prism_time i).

Definition factor_ranks (i : Ordinal 2)
  : nat * nat * nat * nat * nat
  := (fin_rank (staircase_factor i).1,
      fin_rank ((staircase_factor i).2.1 fin_first),
      fin_rank ((staircase_factor i).2.1 fin_first⁺),
      fin_rank ((staircase_factor i).2.1 fin_first⁺⁺),
      fin_rank ((staircase_factor i).2.1 fin_first⁺⁺⁺)).

Example three_actual_staircases_compute
  : (factor_ranks fin_first, factor_ranks fin_first⁺,
     factor_ranks fin_first⁺⁺) =
      ((0, 0, 1, 2, 3), (1, 0, 1, 2, 3), (2, 0, 1, 2, 3)).
Proof. vm_compute. reflexivity. Defined.

(** A six-position spatial simplex repeats all three spatial vertices. *)

Definition repeated_space
  : (@Hom Δ) 5 2
  := σ[2; fin_first] ∘
      (σ[3; fin_first⁺⁺] ∘ σ[4; fin_first⁺⁺⁺⁺]).

Definition repeated_time
  : (@Hom Δ) 5 1%nat
  := SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4).

Definition repeated_factor
  := SimplexPrismFactor repeated_space repeated_time.

Definition six_ranks {m : nat} (h : (@Hom Δ) 5 m)
  : nat * nat * nat * nat * nat * nat
  := (fin_rank (h fin_first), fin_rank (h fin_first⁺),
      fin_rank (h fin_first⁺⁺), fin_rank (h fin_first⁺⁺⁺),
      fin_rank (h fin_first⁺⁺⁺⁺), fin_rank (h fin_first⁺⁺⁺⁺⁺)).

Example high_degenerate_factor_computes
  : (six_ranks repeated_space, six_ranks repeated_time,
     fin_rank repeated_factor.1, six_ranks repeated_factor.2.1) =
      ((0, 0, 1, 1, 2, 2), (0, 0, 0, 1, 1, 1), 1, (0, 0, 1, 2, 3, 3)).
Proof. vm_compute. reflexivity. Defined.

Definition zero_time
  : (@Hom Δ) 5 1%nat
  := ConstF [Ord 5] (C := [Ord 1]) fin_first.

Definition one_time
  : (@Hom Δ) 5 1%nat
  := ConstF [Ord 5] (C := [Ord 1]) fin_first⁺.

Example extreme_times_compute
  : (fin_rank (SimplexPrismFactor repeated_space zero_time).1,
     six_ranks (SimplexPrismFactor repeated_space zero_time).2.1,
     fin_rank (SimplexPrismFactor repeated_space one_time).1,
     six_ranks (SimplexPrismFactor repeated_space one_time).2.1) =
      (2, (0, 0, 1, 1, 2, 2), 0, (1, 1, 2, 2, 3, 3)).
Proof. vm_compute. reflexivity. Defined.

Definition last_point
  : (@Hom Δ) 0%nat 3
  := δ[2; fin_first] ∘ (δ[1; fin_first] ∘ δ[0; fin_first]).

Example pivot_can_change_under_restriction
  : (fin_rank (simplex_prism_pivot σ[2; fin_first⁺⁺]
        (two_sphere_prism_time fin_first⁺⁺)),
     fin_rank (simplex_prism_pivot (σ[2; fin_first⁺⁺] ∘ last_point)
       (two_sphere_prism_time fin_first⁺⁺ ∘ last_point)),
     fin_rank (SimplexPrismIndexF (σ[2; fin_first⁺⁺] ∘ last_point)
       (two_sphere_prism_time fin_first⁺⁺ ∘ last_point) fin_first)) = (2, 0, 3).
Proof. vm_compute. reflexivity. Defined.

(** Both coordinate equations and factor uniqueness consume the actual
    existential witnesses, including the five-dimensional input. *)

Definition repeated_space_equation
  := fst repeated_factor.2.2.

Definition repeated_time_equation
  := snd repeated_factor.2.2.

Definition repeated_factor_unique
  : repeated_factor.2.1 ≈ SimplexPrismIndexF repeated_space repeated_time
  := simplex_prism_factor_unique repeated_factor.1 repeated_space
      repeated_time repeated_factor.2.1 repeated_space_equation
      repeated_time_equation.

Definition restricted_factor_equation
  := simplex_prism_index_pre last_point σ[2; fin_first⁺⁺]
      (two_sphere_prism_time fin_first⁺⁺).

(** A supplied last-staircase factor overlaps the automatically selected
    first staircase. Uniqueness compares factors, not their pivots. *)

Definition overlapping_factor_unique
  := simplex_prism_factor_unique (fin_first⁺⁺ : Ordinal 2)
      (σ[2; fin_first⁺⁺] ∘ last_point)
      (SimplexPrismTimeF fin_first⁺⁺ ∘ last_point) last_point
      (reflexivity _) (reflexivity _).

(** The empty maximum and zero-dimensional spatial cylinder both compute. *)

Example empty_maximum_computes
  : fin_rank (finite_ordinal_max 0
      (λ i : Fin@{Set} 0, match i with end) : Ordinal 4) = 0.
Proof. vm_compute. reflexivity. Defined.

Example point_cylinder_computes
  : (fin_rank (SimplexPrismFactor
       (ConstF [Ord 5] (C := [Ord 0]) fin_first) repeated_time).1,
     six_ranks (SimplexPrismFactor
       (ConstF [Ord 5] (C := [Ord 0]) fin_first) repeated_time).2.1) =
      (0, (0, 0, 0, 1, 1, 1)).
Proof. vm_compute. reflexivity. Defined.

(** ** Determining Maps and Existing Relative Cylinders

    The actual product cylinder supplies a map without any Kan data.
    The existing nonzero Boolean sphere supplies an actual relative
    cylinder; its evaluation theorem likewise requires no fillers. *)

Definition triangle_cylinder
  : Fct (Δ^op) SetCat
  := SimplicialCylinderF (Δ[2]).

Definition identity_cylinder_factor
  := simplex_prism_eval_factor (IdN : triangle_cylinder ⇒ triangle_cylinder)
      repeated_space repeated_time.

Definition identity_cylinder_determined
  := snd (simplex_prism_map_eq_iff
      (IdN : triangle_cylinder ⇒ triangle_cylinder) IdN)
      (λ k, reflexivity (simplex_prism_eval
        (IdN : triangle_cylinder ⇒ triangle_cylinder) k)).

Definition reconstructed_product_value
  : triangle_cylinder 5
  := triangle_cylinder[SimplexPrismIndexF repeated_space repeated_time]Δ
      (simplex_prism_eval (IdN : triangle_cylinder ⇒ triangle_cylinder)
        (simplex_prism_pivot repeated_space repeated_time)).

Example actual_product_coordinates_compute
  : (six_ranks (lower (fst reconstructed_product_value)),
     six_ranks (lower (snd reconstructed_product_value))) =
      ((0, 0, 1, 1, 2, 2), (0, 0, 0, 1, 1, 1)).
Proof. vm_compute. reflexivity. Defined.

Fail Definition unchosen_Boolean_Kan
  : HasKanFillers BoolCocycleModel
  := _.


Definition actual_sphere_cylinder
  : TwoSphereCylinderHomotopy BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      bool_cocycle_sphere bool_cocycle_sphere.
Proof.
  apply TwoSphereConstantCylinder.
  change (bool_cocycle_sphere.1 ≈S bool_cocycle_sphere.1). reflexivity.
Defined.

Definition actual_sphere_factor
  := two_sphere_cylinder_factor actual_sphere_cylinder
      repeated_space repeated_time.

Definition actual_legacy_time_comparison
  := two_sphere_prism_time_eq fin_first⁺.

Fail Definition still_unchosen_Boolean_Kan
  : HasKanFillers BoolCocycleModel
  := _.
