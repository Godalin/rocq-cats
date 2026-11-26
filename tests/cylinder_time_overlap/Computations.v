From Cats Require Import
  Instance.Set.Simplicial.Homotopy.TimeOverlap
  Instance.Set.Simplicial.TriangleInput
  Cat.Diagram.Core
  Cat.Core.
From Stdlib Require Import
  Lists.List.

Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Local and Global Intersection Vertices

    Enumerate every ordered pair. The local omitted position is not the
    common vertex; applying its zero-dimensional coface recovers it. *)

Definition distinct_pairs
  : list (∃ j k : Ordinal 2, ¬ j = k).
Proof.
  refine [_; _; _; _; _; _].
  - refine (fin_first; (fin_first⁺; _)); discriminate.
  - refine (fin_first; (fin_first⁺⁺; _)); discriminate.
  - refine (fin_first⁺; (fin_first; _)); discriminate.
  - refine (fin_first⁺; (fin_first⁺⁺; _)); discriminate.
  - refine (fin_first⁺⁺; (fin_first; _)); discriminate.
  - refine (fin_first⁺⁺; (fin_first⁺; _)); discriminate.
Defined.

Example six_local_vertices
  : map (λ q : (∃ j k : Ordinal 2, ¬ j = k),
      (fin_rank (triangle_time_overlap_vertex q.1 q.2.1 q.2.2),
      fin_rank (triangle_time_overlap_vertex q.2.1 q.1
        (λ E, q.2.2 (symmetry E))))) distinct_pairs =
      [(1, 1); (0, 1); (1, 1); (0, 0); (1, 0); (0, 0)].
Proof. vm_compute. reflexivity. Defined.

Example six_global_vertices
  : map (λ q : (∃ j k : Ordinal 2, ¬ j = k), fin_rank (δ[1; q.1]
      (triangle_time_overlap_vertex q.1 q.2.1 q.2.2))) distinct_pairs =
      [2; 1; 2; 0; 1; 0].
Proof. vm_compute. reflexivity. Defined.

Program Definition face_time (j : Ordinal 2)
  : SimplicialCylinderF (Δ[2]) ⇒ (Δ[2])
  :=
  {|nt n := {|func x := {|lower := δ[1; j] ∘ lower (snd x)|}|}
  |}.
Next Obligation.
  intros [a t] [a' t'] [E F]. refine {|lower := _|}.
  exact (@comp_l Δ n 1%nat 2 δ[1; j] (lower t) (lower t') (lower F)).
Defined.
Next Obligation.
  intros x. refine {|lower := _|}. symmetry.
  exact (@comp_assoc Δ Y X 1%nat 2 δ[1; j] (lower (snd x)) f).
Defined.

Definition time_endpoints (r : Ordinal 2)
  : cylinder_time_endpoint_matching r face_time.
Proof.
  intros j k Hj Hk E n a. refine {|lower := _|}.
  apply (snd (simplex_eq_iff _ _)). intros z.
  exact (fst (simplex_eq_iff _ _) (coface_intersection_swap j k E) fin_first).
Defined.

Definition actual_common_factors (r : Ordinal 2)
  : triangle_input_face_agreement r face_time
  := cylinder_time_factors_from_endpoints r face_time (time_endpoints r).

Definition high_space
  : (Δ[2]) 5
  := {|lower := δ[1; fin_first⁺] ∘
      (σ[1; fin_first] ∘ σ[2; fin_first] ∘
        σ[3; fin_first] ∘ σ[4; fin_first])|}.

Definition time_at (n : nat) (v : Ordinal 1%nat)
  : (Δ[1]) n
  := {|lower := ConstF [Ord n] (C := [Ord 1%nat]) v|}.

Definition six_ranks (t : (Δ[2]) 5)
  : list nat
  := map (λ z : Ordinal 5, fin_rank (lower t z))
      ((fin_first : Ordinal 5) :: fin_first⁺ :: fin_first⁺⁺ :: fin_first⁺⁺⁺ ::
        fin_first⁺⁺⁺⁺ :: fin_first⁺⁺⁺⁺⁺ :: nil).

Example high_dimensional_time_values
  : map (λ q : (∃ j k : Ordinal 2, ¬ j = k), six_ranks (face_time q.1 5
      (high_space, time_at 5
        (triangle_time_overlap_vertex q.1 q.2.1 q.2.2)))) distinct_pairs =
      [repeat 2 6; repeat 1 6; repeat 2 6;
       repeat 0 6; repeat 1 6; repeat 0 6].
Proof. vm_compute. reflexivity. Defined.

Example spatial_coordinate_is_nonconstant
  : six_ranks high_space = [0; 0; 0; 0; 0; 2].
Proof. vm_compute. reflexivity. Defined.

Definition actual_high_factor_client
  : face_time fin_first 5 (high_space, time_at 5 fin_first⁺) ≈S
      face_time fin_first⁺ 5 (high_space, time_at 5 fin_first⁺).
Proof.
  apply (actual_common_factors fin_first⁺⁺); try discriminate.
  apply (snd (simplex_eq_iff _ _)). intros z. reflexivity.
Defined.

(** ** Specified Equality with Distinct Native Values

    Endpoint laws have independent Boolean witnesses. Forward/backward
    transport must preserve their Type-valued relation, not native equality. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation. split; red; intros; exact true. Defined.

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Program Definition face_value (j : Ordinal 2)
  : SimplicialCylinderF (Δ[2]) ⇒ W
  :=
  {|nt n := {|func x := negb (Nat.eqb (fin_rank j) 0)|}
  |}.
Next Obligation. intros a b E. exact false. Defined.
Next Obligation. intros a. exact true. Defined.

Definition value_endpoints (r : Ordinal 2) (v : bool)
  : cylinder_time_endpoint_matching r face_value.
Proof. intros j k Hj Hk E n a. exact v. Defined.

Definition value_factors (r : Ordinal 2) (v : bool)
  : cylinder_time_factor_matching r face_value
  := cylinder_time_factors_from_endpoints r face_value (value_endpoints r v).

Definition independent_endpoint_witnesses (r : Ordinal 2) (v : bool)
  : cylinder_time_endpoint_matching r face_value
  := cylinder_time_endpoints_from_factors r face_value (value_factors r v).

Definition distinct_related_values
  : face_value fin_first 5 (high_space, time_at 5 fin_first⁺) ≈S
      face_value fin_first⁺ 5 (high_space, time_at 5 fin_first⁺).
Proof.
  apply (value_factors fin_first⁺⁺ false); try discriminate.
  apply (snd (simplex_eq_iff _ _)). intros z. reflexivity.
Defined.

Example endpoint_transport_is_computational (v : bool)
  : independent_endpoint_witnesses fin_first⁺⁺ v fin_first fin_first⁺
      (ltac:(discriminate)) (ltac:(discriminate)) (ltac:(discriminate))
      2 (simplex_generic 2) = true.
Proof. vm_compute. reflexivity. Defined.

Fail Definition native_value_equality
  : face_value fin_first 5 (high_space, time_at 5 fin_first⁺) =
      face_value fin_first⁺ 5 (high_space, time_at 5 fin_first⁺)
  := ltac:(vm_compute; reflexivity).

Fail Definition no_endpoint_input
  : cylinder_time_factor_matching fin_first⁺⁺ face_value
  := cylinder_time_factors_from_endpoints fin_first⁺⁺ face_value.

Fail Definition automatic_kan
  : HasKanFillers W
  := ltac:(typeclasses eauto).

(** ** Incompatible Actual Endpoint Maps

    Constant maps at distinct triangle vertices give a genuine counterexample
    to unconditional factor compatibility. *)

Program Definition bad_time (j : Ordinal 2)
  : SimplicialCylinderF (Δ[2]) ⇒ (Δ[2])
  :=
  {|nt n := {|func x := {|lower := ConstF [Ord n] (C := [Ord 2]) j|}|}
  |}.
Next Obligation. intros x y E. refine {|lower := _|}. reflexivity. Defined.
Next Obligation.
  intros x. refine {|lower := _|}.
  apply (snd (simplex_eq_iff _ _)). intros z. reflexivity.
Defined.

Definition incompatible_endpoints
  : ¬ cylinder_time_endpoint_matching fin_first⁺⁺ bad_time.
Proof.
  intros E.
  assert (H0 : ¬ (fin_first : Ordinal 2) = fin_first⁺⁺) by discriminate.
  assert (H1 : ¬ (fin_first⁺ : Ordinal 2) = fin_first⁺⁺) by discriminate.
  assert (H01 : ¬ (fin_first : Ordinal 2) = fin_first⁺) by discriminate.
  pose proof (E fin_first fin_first⁺ H0 H1 H01 2 (simplex_generic 2)) as F.
  pose proof (fst (simplex_eq_iff _ _) (lower F) fin_first) as G.
  discriminate G.
Defined.

Definition incompatible_factors
  : ¬ cylinder_time_factor_matching fin_first⁺⁺ bad_time
  := λ E, incompatible_endpoints
      (cylinder_time_endpoints_from_factors fin_first⁺⁺ bad_time E).
