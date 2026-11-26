From Cats Require Import
  Instance.Set.Simplicial.TriangleIteration
  Instance.Bool.CocycleKan
  Cat.Diagram.Core
  Cat.Core.
From Stdlib Require Import
  Lists.List.

Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Nine-Step Computations with Distinct Choices

    Boolean equality witnesses permit independently selected cell values.
    In this setoid recovery uses its specified relation, so recovering an
    old map must not be silently strengthened to native value equality. *)

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

Program Definition old_map (r : Ordinal 2)
  : TriangleHornStage r 0 ⇒ W
  :=
  {|nt n := {|func x := true|}
  |}.
Next Obligation. intros x y E. exact false. Defined.
Next Obligation. intros x. exact true. Defined.

Program Definition one_choice (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers W n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m h'. exact true. Defined.

Definition choices (r : Ordinal 2) (v : bool) (s : Ordinal 8)
  : HasHornFillers W (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)
  := one_choice _ _ v.

Definition extension (r : Ordinal 2) (v : bool)
  := TriangleHornProductExtension r (choices r v) (old_map r).

Definition diagonal
  : TriangleHornAmbient 2
  := (simplex_generic 2, simplex_generic 2).

Definition parameters
  : list (Ordinal 2)
  := [(fin_first : Ordinal 2); (fin_first⁺ : Ordinal 2);
      (fin_first⁺⁺ : Ordinal 2)].

Example all_parameter_choices_compute
  : map (λ r, ((extension r false).1 2 diagonal,
               (extension r true).1 2 diagonal)) parameters =
      repeat (false, true) 3.
Proof. vm_compute. reflexivity. Defined.

Definition boundary_factor
  : (@Hom Δ) 2 1%nat
  := σ[1; fin_first].

Definition boundary_space
  : (@Hom Δ) 2 2
  := δ[1; fin_first⁺⁺] ∘ boundary_factor.

Definition old_point (r : Ordinal 2)
  : TriangleHornStage r 0 2.
Proof.
  refine (({|lower := boundary_space|}, simplex_generic 2); _).
  left. left. exists (fin_first⁺⁺). exists boundary_factor. reflexivity.
Defined.

(** Final-stage conversion may change a membership witness. Native
    values can differ in this example even though recovery is valid. *)

Example specified_recovery_is_not_native
  : map (λ r, ((old_map r) 2 (old_point r),
      (extension r false).1 2 (old_point r).1)) parameters =
      repeat (true, false) 3.
Proof. vm_compute. reflexivity. Defined.

Definition chain_value (r : Ordinal 2)
  : bool
  := let e := triangle_horn_chain_extension_target r (choices r false)
        (old_map r) in
      e.1 2 (chain_segment (TriangleHornChain r) fin_first
        (fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺) (ordinal_from_first (fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺))
        2 (old_point r)).

Example actual_chain_old_values_compute
  : map chain_value parameters = repeat true 3.
Proof. vm_compute. reflexivity. Defined.

Definition five_factor
  : (@Hom Δ) 5 2
  := σ[2; fin_first] ∘ σ[3; fin_first] ∘ σ[4; fin_first].

Example degree_five_values_compute
  : map (λ r, (extension r false).1 5
      ({|lower := five_factor|}, {|lower := five_factor|})) parameters =
      repeat false 3.
Proof. vm_compute. reflexivity. Defined.

Definition full_recovery (r : Ordinal 2) (v : bool)
  := (extension r v).2.

Fail Definition full_choices_are_native_equal
  : (extension fin_first false).1 2 diagonal =
      (extension fin_first true).1 2 diagonal
  := ltac:(vm_compute; reflexivity).

Fail Definition old_recovery_is_native
  : (extension fin_first false).1 2 (old_point fin_first).1 =
      (old_map fin_first) 2 (old_point fin_first)
  := ltac:(vm_compute; reflexivity).

Fail Definition iteration_selects_full_kan
  : HasKanFillers (TriangleHornStage fin_first 0)
  := ltac:(typeclasses eauto).

Fail Definition iteration_selects_all_pushouts
  : HasPushout (FctCat (Δ^op) SetCat)
  := ltac:(typeclasses eauto).

(** ** A Genuine Nonzero Cocycle Client

    All nine real horn choices are consumed from the explicit Boolean
    Kan model. Recovery retains the nonzero old two-simplex; the client
    uses the general law, without replacing the computed extension. *)

Program Definition spatial_projection
  : TriangleHornAmbient ⇒ (Δ[2] : Fct (Δ^op) SetCat)
  :=
  {|nt n := {|func x := fst x|}
  |}.
Next Obligation. intros [a b] [a' b'] [E F]. exact E. Defined.
Next Obligation. intros [a b]. reflexivity. Defined.

Definition nonzero_total
  : TriangleHornAmbient ⇒ BoolCocycleModel
  := simplex_map_resp bool_cocycle_triangle ∘Nv spatial_projection.

Definition actual_extension (r : Ordinal 2)
  := TriangleHornProductExtension r
      (λ s, @hasHornFillers BoolCocycleModel BoolCocycleModel_HasKanFillers
        (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s))
      (nonzero_total ∘Nv RegionInclusionN (TriangleHornRegion r 0)).

Definition actual_recovery (r : Ordinal 2)
  := (actual_extension r).2.

Definition cocycle_old_point
  : TriangleHornStage fin_first 0 2.
Proof.
  refine ((simplex_generic 2,
    {|lower := δ[1; fin_first⁺] ∘ boundary_factor|}); _).
  left. right.
  assert (J : ¬ (fin_first⁺ : Ordinal 2) = fin_first).
  { intros E. discriminate E. }
  exists (fin_first⁺; J), boundary_factor. reflexivity.
Defined.

(** First evaluate recovery on an abstract map; specializing this client
    afterward retains the actual computed nine-step extension. *)

Definition nonzero_recovery_from (b : TriangleHornAmbient ⇒ BoolCocycleModel)
    (E : (b ∘Nv RegionInclusionN (TriangleHornRegion fin_first 0)) ≈N
      (nonzero_total ∘Nv RegionInclusionN (TriangleHornRegion fin_first 0)))
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (b 2 cocycle_old_point.1) = true.
Proof.
  transitivity (two_cocycle_triangle_value_resp (M := BoolS_Monoid)
    (nonzero_total 2 cocycle_old_point.1)).
  - exact (@func_proper (BoolCocycleModel 2) BoolS
      (@two_cocycle_triangle_value_resp BoolS_Monoid) _ _
      (E 2 cocycle_old_point)).
  - reflexivity.
Defined.

Definition actual_nonzero_recovery
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      ((actual_extension fin_first).1 2 cocycle_old_point.1) = true
  := nonzero_recovery_from (actual_extension fin_first).1
      (actual_recovery fin_first).
