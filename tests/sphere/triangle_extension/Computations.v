From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereTriangle
  Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder
  Instance.Set.Product
  Cat.Functor.FiniteProducts
  Cat.Diagram.Core
  Cat.Core.
From Stdlib Require Import
  Lia.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Ordered Edges in a Representable Triangle

    Projection onto the actual triangle parameter supplies an extension.
    Its two consecutive edges compose to the long edge without Kan. *)

Definition P
  : Fct (Δ^op) SetCat
  := Δ[0].

Definition point (n : nat)
  : P n
  := {|lower := ConstF [Ord n] (C := [Ord 0]) fin_first|}.

Definition shape_triangle
  : SimplicialParameterF P 2 ⇒ Δ[2]
  := PointwiseSndN (Δ^op) SetCat P (Δ[2]).

Definition shape_first
  := SimplicialTriangleEdge shape_triangle fin_first⁺⁺.

Definition shape_second
  := SimplicialTriangleEdge shape_triangle fin_first.

Definition shape_edge_refl (i : Ordinal 2)
  : simplicial_triangle_edge shape_triangle i ≈N
      simplicial_triangle_edge shape_triangle i.
Proof. reflexivity. Defined.

Definition shape_composite
  := SimplicialTriangleComposite shape_triangle shape_first shape_second
      (shape_edge_refl fin_first⁺⁺) (shape_edge_refl fin_first).

Definition two_ranks (K : SimplicialCylinderF P ⇒ Δ[2])
  : nat * nat
  := let w := lower (K 1 (point 1, simplex_generic 1)) in
      (fin_rank (w fin_first), fin_rank (w fin_first⁺)).

Example actual_triangle_composition
  : (two_ranks (homotopy_map shape_first),
     two_ranks (homotopy_map shape_second),
     two_ranks (homotopy_map shape_composite)) = ((0, 1), (1, 2), (0, 2)).
Proof. vm_compute. reflexivity. Defined.

(** ** An Actual Relative Extension with Independent Witnesses

    Boolean witnesses compare native-distinct data. Start from the
    already integrated elementary construction, retaining its reversed
    direction; a separately supplied triangle then reverses that cylinder. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation.
  split.
  - intros x. exact true.
  - intros x y E. exact E.
  - intros x y z E F. exact E.
Defined.

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Definition x
  : TwoSphereS W false
  := (false; λ i, true).

Definition y
  : TwoSphereS W false
  := (true; λ i, false).

Definition sample_position (n : nat)
  : Ordinal n
  := match n with
  | 0 => fin_first
  | S k => fin_first⁺
  end.

Program Definition triangle
  : SimplicialParameterF (Δ[2]) 2 ⇒ W
  :=
  {|nt n :=
      {|func z := Nat.eqb (fin_rank (lower (snd z) (sample_position n))) 1
      |}
  |}.
Next Obligation. intros z z' E. exact true. Defined.
Next Obligation. intros z. exact false. Defined.

Definition relative_triangle
  : is_two_sphere_triangle_relative W false triangle
  := λ n a t, true.

Definition elementary
  : TwoSphereHomotopy W false y x
  := (false; (false, (true, (true, false)))).

Definition first_cylinder
  : TwoSphereCylinderHomotopy W false x y
  := TwoSphereHomotopyCylinder W false elementary.

Definition first_edge
  : simplicial_triangle_edge triangle fin_first⁺⁺ ≈N
      homotopy_map first_cylinder.1
  := λ n z, true.

Definition constant_edge
  : simplicial_triangle_edge triangle fin_first⁺ ≈N
      homotopy_map (SimplicialConstantHomotopy ⟦x.1⟧Δ[W; 2])
  := λ n z, false.

Definition reversed
  : TwoSphereCylinderHomotopy W false y x
  := SphereTriangleReverse W false triangle relative_triangle first_cylinder
      first_edge constant_edge.

Definition composite
  : TwoSphereCylinderHomotopy W false x x
  := SphereTriangleComposite W false triangle relative_triangle
      first_cylinder reversed first_edge (λ n z, true).

Example reverse_keeps_the_read_edge_definition
  : homotopy_map reversed.1 = simplicial_triangle_edge triangle fin_first
  := eq_refl.

Example composite_keeps_the_read_edge_definition
  : homotopy_map composite.1 = simplicial_triangle_edge triangle fin_first⁺
  := eq_refl.

Definition endpoint_values {a b : TwoSphereS W false}
    (H : TwoSphereCylinderHomotopy W false a b)
  : bool * bool
  := (simplex_element_resp
       (homotopy_map H.1 ∘Nv SimplicialEndpointN (Δ[2]) false),
      simplex_element_resp
       (homotopy_map H.1 ∘Nv SimplicialEndpointN (Δ[2]) true)).

Example actual_reverse_and_composite_endpoints
  : (endpoint_values first_cylinder, endpoint_values reversed,
     endpoint_values composite) = ((false, true), (true, false), (false, false)).
Proof. vm_compute. reflexivity. Defined.

Definition other_reversed
  := SphereTriangleReverse W false triangle (λ n a t, false) first_cylinder
      (λ n z, false) (λ n z, true).

Example independent_laws_leave_the_actual_map_unchanged
  : homotopy_map reversed.1 = homotopy_map other_reversed.1
  := eq_refl.

Definition boundary_datum
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘
        SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4);
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺]
        (SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4))
        (boundary_face_member fin_first⁺))|}.

Definition all_time_reverse_boundary
  := reversed.2 5 boundary_datum
      {|lower := SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Definition all_time_composite_boundary
  := composite.2 5 boundary_datum
      {|lower := SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4)|}.

Definition equal_extensions_give_equal_edges
  : simplicial_triangle_edge triangle fin_first ≈N
      simplicial_triangle_edge triangle fin_first
  := simplicial_triangle_edge_proper triangle triangle (λ n z, false) fin_first.

Fail Definition no_automatic_Kan
  : HasKanFillers W
  := _.

Fail Definition no_automatic_horn
  : HasHornFillers W 4 fin_first
  := _.

Fail Definition no_directed_equivalence
  : Equivalence (TwoSphereCylinderHomotopy W false)
  := _.

(** ** Not Every Pair of Edges Has a Triangle Extension

    In the interval, retaining edge 01 and making 02 constant at zero
    would require a monotone triangle with vertex values (0,1,0).
    This is impossible. The extension input cannot be dropped. *)

Definition interval_first
  : SimplicialCylinderF P ⇒ Δ[1]
  := PointwiseSndN (Δ^op) SetCat P (Δ[1]).

Program Definition interval_zero
  : SimplicialCylinderF P ⇒ Δ[1]
  :=
  {|nt n :=
      {|func z := {|lower := ConstF [Ord n] (C := [Ord 1]) fin_first|}
      |}
  |}.
Next Obligation. intros z z' E. refine {|lower := _|}. reflexivity. Defined.
Next Obligation.
  intros z. refine {|lower := _|}.
  apply (snd (simplex_eq_iff _ _)). intros j. reflexivity.
Defined.

Example interval_reverse_extension_is_impossible
  : ¬ (∃ T : SimplicialParameterF P 2 ⇒ Δ[1],
      (simplicial_triangle_edge T fin_first⁺⁺ ≈N interval_first) ∧
      (simplicial_triangle_edge T fin_first⁺ ≈N interval_zero)).
Proof.
  intros [T [E01 E02]].
  pose (z := (point 2, simplex_generic 2)).
  pose (v := lower (T 2 z)).
  assert (F : ∀ i : Ordinal 2,
    simplicial_triangle_edge T i 1 (point 1, simplex_generic 1) ≈S
      (Δ[1])[δ[1; i]]Δ (T 2 z)).
  { intros i. transitivity (T 1 ((SimplicialParameterF P 2)[δ[1; i]]Δ z)).
    - apply (@func_proper _ _ (T 1)). split; refine {|lower := _|}.
      + apply (snd (simplex_eq_iff _ _)). intros [[] | [[] | []]]; reflexivity.
      + change (δ[1; i] ∘ (@Cat.Core.id Δ 1%nat) ≈
          (@Cat.Core.id Δ 2) ∘ δ[1; i]).
        rewrite comp_id_r, comp_id_l. reflexivity.
    - apply simplex_restrict_natural. }
  assert (G1 : v fin_first⁺ = fin_first⁺).
  { pose (E := transitivity (symmetry (F fin_first⁺⁺))
      (E01 1 (point 1, simplex_generic 1))).
    exact (fst (simplex_eq_iff _ _) (lower E) fin_first⁺). }
  assert (G2 : v fin_first⁺⁺ = fin_first).
  { pose (E := transitivity (symmetry (F fin_first⁺))
      (E02 1 (point 1, simplex_generic 1))).
    exact (fst (simplex_eq_iff _ _) (lower E) fin_first⁺). }
  pose proof (ordinal_fct_monotone v fin_first⁺ fin_first⁺⁺
    ltac:(cbn; repeat constructor)) as L.
  rewrite G1, G2 in L. cbn in L. lia.
Defined.
