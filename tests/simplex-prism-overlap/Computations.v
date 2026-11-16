From Cats Require Import
  Instance.Set.Simplicial.PrismOverlap
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Shared-Face Mediators

    Repeat every spatial vertex in a degree-five input. The two factor
    records may differ, but the computed mediator recovers both in the
    specified operator equality. *)

(** * 实际共享面中介

    在五维输入中重复每个空间顶点。两个因子记录可以不同，计算所得中介按
    指定算子相等同时恢复二者。 *)

Definition repeated_shape
  : (@Hom Δ) 5 2
  := σ[2; fin_first] ∘
      (σ[3; fin_first⁺⁺] ∘ σ[4; fin_first⁺⁺⁺⁺]).

Definition left_factor (i : Ordinal 1)
  : (@Hom Δ) 5 3
  := δ[2; i↑⁺] ∘ repeated_shape.

Definition right_factor (i : Ordinal 1)
  : (@Hom Δ) 5 3
  := δ[2; i↑⁺] ∘ ((id : (@Hom Δ) 2 2) ∘ repeated_shape).

Definition common_space (i : Ordinal 1)
  : σ[2; i↑] ∘ left_factor i ≈ σ[2; i⁺] ∘ right_factor i.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros j.
  destruct i as [[] | [[] | []]],
    j as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; reflexivity.
Defined.

Definition common_time (i : Ordinal 1)
  : SimplexPrismTimeF i↑ ∘ left_factor i ≈
      SimplexPrismTimeF i⁺ ∘ right_factor i.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros j.
  destruct i as [[] | [[] | []]],
    j as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; reflexivity.
Defined.

Definition adjacent_factor (i : Ordinal 1)
  := SimplexPrismAdjacentFactor i (left_factor i) (right_factor i)
      (common_space i) (common_time i).

Definition six_ranks {m : nat} (f : (@Hom Δ) 5 m)
  : nat * nat * nat * nat * nat * nat
  := (fin_rank (f fin_first), fin_rank (f fin_first⁺),
      fin_rank (f fin_first⁺⁺), fin_rank (f fin_first⁺⁺⁺),
      fin_rank (f fin_first⁺⁺⁺⁺), fin_rank (f fin_first⁺⁺⁺⁺⁺)).

Example both_mediators_compute
  : (six_ranks (adjacent_factor fin_first).1,
     six_ranks (adjacent_factor fin_first⁺).1) =
      ((0, 0, 1, 1, 2, 2), (0, 0, 1, 1, 2, 2)).
Proof. vm_compute. reflexivity. Defined.

Example actual_coface_recoveries_compute
  : (six_ranks (δ[2; fin_first⁺] ∘ (adjacent_factor fin_first).1),
     six_ranks (δ[2; fin_first⁺⁺] ∘ (adjacent_factor fin_first⁺).1)) =
      ((0, 0, 2, 2, 3, 3), (0, 0, 1, 1, 3, 3)).
Proof. vm_compute. reflexivity. Defined.

Definition left_recovery (i : Ordinal 1)
  := fst (adjacent_factor i).2.

Definition right_recovery (i : Ordinal 1)
  := snd (adjacent_factor i).2.

(** ** An Outer Overlap and Distinct Value Witnesses

    The first/last pieces meet at positions zero and three. Use a real
    high-degree factor through that edge, then transport supplied Boolean
    equality witnesses through the actual middle value. *)

(** ** 首尾交叠与不同取值见证

    首尾两块在位置零与三处相交。使用经过此边的实际高维因子，再经过实际
    中间值运输给定布尔相等见证。 *)

Definition edge_time
  : (@Hom Δ) 5 1%nat
  := SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4).

Definition outer_left
  : (@Hom Δ) 5 3
  := (δ[2; fin_first⁺] ∘ δ[1; fin_first⁺]) ∘ edge_time.

Definition outer_right
  : (@Hom Δ) 5 3
  := outer_left ∘ (id : (@Hom Δ) 5 5).

Definition outer_space
  : σ[2; fin_first] ∘ outer_left ≈ σ[2; fin_first⁺⁺] ∘ outer_right.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros j.
  destruct j as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; reflexivity.
Defined.

Definition outer_time
  : SimplexPrismTimeF fin_first ∘ outer_left ≈
      SimplexPrismTimeF fin_first⁺⁺ ∘ outer_right.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros j.
  destruct j as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; reflexivity.
Defined.

Definition actual_middle_coordinates
  := simplex_prism_outer_middle outer_left outer_right outer_space outer_time.

Example outer_factor_computes
  : (six_ranks outer_left, six_ranks outer_right) =
      ((0, 0, 0, 3, 3, 3), (0, 0, 0, 3, 3, 3)).
Proof. vm_compute. reflexivity. Defined.

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

Definition WitnessX
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Definition values (i : Ordinal 2)
  : WitnessX 3
  := match i with inl _ => false | inr _ => true end.

Definition first_equation
  : d[WitnessX; 2; fin_first⁺] (values fin_first) ≈S
      d[WitnessX; 2; fin_first⁺] (values fin_first⁺)
  := false.

Definition second_equation
  : d[WitnessX; 2; fin_first⁺⁺] (values fin_first⁺) ≈S
      d[WitnessX; 2; fin_first⁺⁺] (values fin_first⁺⁺)
  := true.

Definition actual_outer_value_comparison
  := simplex_triangle_prism_outer_overlap values first_equation
      second_equation outer_left outer_right outer_space outer_time.

Definition all_value_overlaps
  := snd (simplex_triangle_prism_overlap_iff values)
      (first_equation, second_equation).

Definition recovered_equations
  := fst (simplex_triangle_prism_overlap_iff values) all_value_overlaps.

Example outer_values_compute
  : (WitnessX[outer_left]Δ (values fin_first),
     WitnessX[outer_right]Δ (values fin_first⁺⁺)) = (false, true).
Proof. vm_compute. reflexivity. Defined.

(** ** Spatial Coordinates Alone Do Not Describe an Intersection

    The two constant factors below have equal spatial images but opposite
    time images. Omitting the time equation would incorrectly identify them. *)

(** ** 仅空间坐标不能描述交叠

    下方两个常值因子的空间像相等，时间像却相反。省略时间方程会错误地识别
    它们。 *)

Definition left_point
  : (@Hom Δ) 0%nat 3
  := ConstF [Ord 0] (C := [Ord 3]) fin_first⁺.

Definition right_point
  : (@Hom Δ) 0%nat 3
  := ConstF [Ord 0] (C := [Ord 3]) fin_first.

Definition only_space_agrees
  : σ[2; fin_first] ∘ left_point ≈ σ[2; fin_first⁺] ∘ right_point.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros [[] | []]. reflexivity.
Defined.

Example times_really_differ
  : ¬ (SimplexPrismTimeF fin_first ∘ left_point ≈
      SimplexPrismTimeF fin_first⁺ ∘ right_point).
Proof.
  intros E. pose proof (fst (simplex_eq_iff _ _) E fin_first) as H.
  discriminate H.
Defined.

Example supplied_factors_really_differ
  : ¬ left_point ≈ right_point.
Proof.
  intros E. pose proof (fst (simplex_eq_iff _ _) E fin_first) as H.
  discriminate H.
Defined.

(** Time equality alone is insufficient as well. *)

(** 仅时间相等也不足够。 *)

Definition only_time_agrees
  : SimplexPrismTimeF fin_first ∘ right_point ≈
      SimplexPrismTimeF fin_first⁺ ∘ left_point.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros [[] | []]. reflexivity.
Defined.

Example spaces_really_differ
  : ¬ (σ[2; fin_first] ∘ right_point ≈ σ[2; fin_first⁺] ∘ left_point).
Proof.
  intros E. pose proof (fst (simplex_eq_iff _ _) E fin_first) as H.
  discriminate H.
Defined.

(** ** Compatibility of Actual Cylinder Values

    Read the two necessary equations from the actual product cylinder.
    Also consume the optional criterion in a nontrivial cocycle target,
    without enabling Kan fillers. *)

(** ** 实际柱值的相容性

    从实际积柱读取两条必要方程；另在非平凡 cocycle 目标消费可选相容条件，
    不启用 Kan 填充。 *)

Definition triangle_cylinder
  : Fct (Δ^op) SetCat
  := SimplicialCylinderF (Δ[2]).

Definition actual_values
  := simplex_prism_eval (IdN : triangle_cylinder ⇒ triangle_cylinder).

Definition actual_first_equation
  := simplex_prism_values_adjacent (IdN : triangle_cylinder ⇒ triangle_cylinder)
      fin_first.

Definition actual_second_equation
  := simplex_prism_values_adjacent (IdN : triangle_cylinder ⇒ triangle_cylinder)
      fin_first⁺.

Definition actual_cylinder_outer_overlap
  := simplex_triangle_prism_outer_overlap actual_values
      actual_first_equation actual_second_equation
      outer_left outer_right outer_space outer_time.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.


Definition constant_sphere_map
  : SimplicialCylinderF (Δ[2]) ⇒ BoolCocycleModel
  := homotopy_map (SimplicialConstantHomotopy (⟦bool_cocycle_sphere.1⟧Δ[BoolCocycleModel; 2])).

Definition cocycle_values
  := simplex_prism_eval constant_sphere_map.

Definition actual_cocycle_compatibility
  := snd (simplex_triangle_prism_overlap_iff cocycle_values)
      (simplex_prism_values_adjacent constant_sphere_map fin_first,
       simplex_prism_values_adjacent constant_sphere_map fin_first⁺).

Fail Definition still_unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.
