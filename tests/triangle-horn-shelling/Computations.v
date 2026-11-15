From Cats Require Import
  Instance.Set.Simplicial.TriangleHorn
  Instance.Set.Simplicial.Horn
  Cat.Core.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * All Three Nine-Step Orders and High-Degree Horn Factors *)

(** * 三个九步次序及高维 horn 因子 *)

Definition nine_results {A : Type} (f : Ordinal 8 → A)
  : A * A * A * A * A * A * A * A * A
  := (f fin_first, f fin_first⁺, f fin_first⁺⁺, f fin_first⁺⁺⁺,
      f fin_first⁺⁺⁺⁺, f fin_first⁺⁺⁺⁺⁺, f fin_first⁺⁺⁺⁺⁺⁺,
      f fin_first⁺⁺⁺⁺⁺⁺⁺, f fin_first⁺⁺⁺⁺⁺⁺⁺⁺).

Definition order_data (r : Ordinal 2)
  := nine_results (λ s, (S (simplex_triangle_horn_face_dim s),
      fin_rank (simplex_triangle_horn_missing r s))).

Example all_three_orders_compute
  : (order_data fin_first, order_data fin_first⁺, order_data fin_first⁺⁺) =
      (((3,0),(3,1),(3,0),(4,0),(4,1),(4,0),(4,2),(4,1),(4,0)),
       ((3,1),(3,1),(3,2),(4,1),(4,1),(4,1),(4,2),(4,2),(4,3)),
       ((3,1),(3,1),(3,2),(4,2),(4,1),(4,1),(4,3),(4,2),(4,4))).
Proof. vm_compute. reflexivity. Defined.

Definition retained_position (r : Ordinal 2) (s : Ordinal 8)
  : Ordinal (S (simplex_triangle_horn_face_dim s))
  := if Nat.eqb (fin_rank (simplex_triangle_horn_missing r s)) 0
      then fin_first⁺ else fin_first.

Definition retained_position_other (r : Ordinal 2) (s : Ordinal 8)
  : ¬ retained_position r s = simplex_triangle_horn_missing r s.
Proof.
  destruct r as [[] | [[] | [[] | []]]],
    s as [[] | [[] | [[] | [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]]]];
    discriminate.
Defined.

Definition repeated (s : Ordinal 8)
  : (@Hom Δ) 5 (simplex_triangle_horn_face_dim s)
  := match Nat.ltb (fin_rank s) 3 as b
      return (@Hom Δ) 5 (if b then 2 else 3) with
    | true => σ[2; fin_first] ∘ (σ[3; fin_first⁺⁺] ∘ σ[4; fin_first⁺⁺⁺⁺])
    | false => σ[3; fin_first] ∘ σ[4; fin_first⁺⁺⁺⁺]
    end.

Definition horn_operator (r : Ordinal 2) (s : Ordinal 8)
  : (@Hom Δ) 5 (S (simplex_triangle_horn_face_dim s))
  := δ[simplex_triangle_horn_face_dim s; retained_position r s] ∘ repeated s.

Definition actual_horn_member (r : Ordinal 2) (s : Ordinal 8)
  : horn_operator r s ∈Sv HornSieve (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)
  := ((retained_position r s; retained_position_other r s);
      (repeated s; reflexivity (horn_operator r s))).

Definition old_coordinates (r : Ordinal 2) (s : Ordinal 8)
  := triangle_horn_stage_from_horn r s (horn_operator r s)
      (actual_horn_member r s).

Definition recovered_horn (r : Ordinal 2) (s : Ordinal 8)
  := triangle_horn_stage_reflect r s (horn_operator r s) (old_coordinates r s).

Definition six_ranks {m : nat} (f : (@Hom Δ) 5 m)
  : nat * nat * nat * nat * nat * nat
  := (fin_rank (f fin_first), fin_rank (f fin_first⁺),
      fin_rank (f fin_first⁺⁺), fin_rank (f fin_first⁺⁺⁺),
      fin_rank (f fin_first⁺⁺⁺⁺), fin_rank (f fin_first⁺⁺⁺⁺⁺)).

(** Actual data of the reflected horn, never equality of its law fields. *)

(** 反映所得 horn 的实际数据，不比较定律字段相等。 *)

Example all_twenty_seven_horn_recoveries_compute
  : ∀ r s, six_ranks
      (δ[simplex_triangle_horn_face_dim s; (recovered_horn r s).1.1] ∘
        (recovered_horn r s).2.1) = six_ranks (horn_operator r s).
Proof.
  intros [[] | [[] | [[] | []]]]
    [[] | [[] | [[] | [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]]]];
    vm_compute; reflexivity.
Defined.

(** The final factor reconstructs both coordinates of every original
    maximal staircase, including on degenerate degree-eight inputs. *)

(** 最终因子重构每个原始最大阶梯的双坐标，包括八维退化输入。 *)

Definition repeated_four
  : (@Hom Δ) 8 4
  := σ[4; fin_first] ∘ (σ[5; fin_first⁺⁺] ∘
      (σ[6; fin_first⁺⁺⁺⁺] ∘ σ[7; fin_first⁺⁺⁺⁺⁺⁺])).

Definition final_membership (r : Ordinal 2) (i : Ordinal 5)
  := triangle_horn_stage_complete r
      (SimplexTriangleProductSpaceF i ∘ repeated_four)
      (SimplexTriangleProductTimeF i ∘ repeated_four).

Definition final_cell_index (r : Ordinal 2) (i : Ordinal 5)
  : nat
  := match final_membership r i with
    | inl _ => 99
    | inr x => fin_rank x.1
    end.

Example all_eighteen_final_indices_compute
  : ∀ r i, final_cell_index r i =
      fin_rank (simplex_triangle_horn_maximal_step r i).
Proof.
  intros [[] | [[] | [[] | []]]]
    [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; vm_compute; reflexivity.
Defined.

Fail Definition no_automatic_Kan
  : HasKanFillers (SimplicialParameterF (Δ[2]) 2)
  := _.

Fail Definition no_automatic_products
  : HasProduct SetCat
  := _.

Definition final_coordinate_data (r : Ordinal 2) (i : Ordinal 5)
    (z : Ordinal 8)
  : nat * nat
  := match final_membership r i with
    | inl _ => (99,99)
    | inr x =>
        (fin_rank (SimplexTriangleHornSpaceF r x.1 ((snd x.2).1 z)),
         fin_rank (SimplexTriangleHornTimeF r x.1 ((snd x.2).1 z)))
    end.

Example both_final_coordinates_compute
  : ∀ r i z, final_coordinate_data r i z =
      (fin_rank (SimplexTriangleProductSpaceF i (repeated_four z)),
       fin_rank (SimplexTriangleProductTimeF i (repeated_four z))).
Proof.
  intros [[] | [[] | [[] | []]]]
    [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]
    [[] | [[] | [[] | [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]]]];
    vm_compute; reflexivity.
Defined.

(** A maximal four-simplex cannot simply be attached first: another
    facet, retained by that proposed horn, is still absent from the base. *)

(** 不能直接从最大四单形开始附着：该候选 horn 的另一个保留面仍不属于初始域。 *)

Definition maximal_cell_cannot_start
  : ¬ is_triangle_horn_stage (fin_first⁺ : Ordinal 2) 0%nat
      (SimplexTriangleHornSpaceF fin_first⁺ (fin_first⁺⁺⁺ : Ordinal 8) ∘
        δ[3; fin_first⁺⁺])
      (SimplexTriangleHornTimeF fin_first⁺ (fin_first⁺⁺⁺ : Ordinal 8) ∘
        δ[3; fin_first⁺⁺]).
Proof.
  intros H. apply (triangle_horn_cell_not_old fin_first⁺
    (fin_first⁺ : Ordinal 8)).
  exact (triangle_horn_stage_mono fin_first⁺ 0%nat 1%nat (Nat.le_0_l 1)
    _ _ H).
Defined.
