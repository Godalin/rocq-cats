From Cats Require Import
  Instance.Set.Simplicial.TriangleProduct
  Instance.Set.Simplicial.Horn
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Staircases, Degenerate Inputs and Shared Facets *)

(** * 实际阶梯、退化输入及共享面 *)

Definition six_results {A : Type} (f : Ordinal 5 → A)
  : A * A * A * A * A * A
  := (f fin_first, f fin_first⁺, f fin_first⁺⁺,
      f fin_first⁺⁺⁺, f fin_first⁺⁺⁺⁺, f fin_first⁺⁺⁺⁺⁺).

Definition five_vertices (i : Ordinal 5)
  : (nat * nat) * (nat * nat) * (nat * nat) * (nat * nat) * (nat * nat)
  := let f := λ j, (fin_rank (SimplexTriangleProductSpaceF i j),
                    fin_rank (SimplexTriangleProductTimeF i j)) in
      (f fin_first, f fin_first⁺, f fin_first⁺⁺,
       f fin_first⁺⁺⁺, f fin_first⁺⁺⁺⁺).

Example all_six_paths_compute
  : six_results five_vertices =
      (((0,0),(0,1),(0,2),(1,2),(2,2)),
       ((0,0),(0,1),(1,1),(1,2),(2,2)),
       ((0,0),(0,1),(1,1),(2,1),(2,2)),
       ((0,0),(1,0),(1,1),(1,2),(2,2)),
       ((0,0),(1,0),(1,1),(2,1),(2,2)),
       ((0,0),(1,0),(2,0),(2,1),(2,2))).
Proof. vm_compute. reflexivity. Defined.

Definition nine_ranks {m : nat} (f : (@Hom Δ) 8 m)
  : nat * nat * nat * nat * nat * nat * nat * nat * nat
  := (fin_rank (f fin_first), fin_rank (f fin_first⁺),
      fin_rank (f fin_first⁺⁺), fin_rank (f fin_first⁺⁺⁺),
      fin_rank (f fin_first⁺⁺⁺⁺), fin_rank (f fin_first⁺⁺⁺⁺⁺),
      fin_rank (f fin_first⁺⁺⁺⁺⁺⁺), fin_rank (f fin_first⁺⁺⁺⁺⁺⁺⁺),
      fin_rank (f fin_first⁺⁺⁺⁺⁺⁺⁺⁺)).

Definition repeated_shape
  : (@Hom Δ) 8 4
  := σ[4; fin_first] ∘ (σ[5; fin_first⁺⁺] ∘
      (σ[6; fin_first⁺⁺⁺⁺] ∘ σ[7; fin_first⁺⁺⁺⁺⁺⁺])).

Definition repeated_factor (i : Ordinal 5)
  := SimplexTriangleProductFactor
      (SimplexTriangleProductSpaceF i ∘ repeated_shape)
      (SimplexTriangleProductTimeF i ∘ repeated_shape).

Example all_six_high_degree_factors_compute
  : six_results (λ i, (fin_rank (repeated_factor i).1,
      nine_ranks (repeated_factor i).2.1)) =
      ((0,(0,0,1,1,2,2,3,3,4)), (1,(0,0,1,1,2,2,3,3,4)),
       (2,(0,0,1,1,2,2,3,3,4)), (3,(0,0,1,1,2,2,3,3,4)),
       (4,(0,0,1,1,2,2,3,3,4)), (5,(0,0,1,1,2,2,3,3,4))).
Proof. vm_compute. reflexivity. Defined.

(** ** Actual Shared-Face Mediators

    The input factors have different operator presentations. Both
    coordinates are supplied, and the constructed mediator is computed
    on a degree-five input, not only on the facet's three-simplex. *)

(** ** 实际共享面中介

    输入因子使用不同算子表达，提供两个坐标方程。计算中介作用于五维输入，
    不仅检查该面的三单形。 *)

Definition repeated_shared
  : (@Hom Δ) 5 3
  := σ[3; fin_first] ∘ σ[4; fin_first⁺⁺⁺⁺].

Definition shared_left (e : Ordinal 5)
  : (@Hom Δ) 5 4
  := δ[3; snd (simplex_triangle_product_adjacency e)] ∘ repeated_shared.

Definition shared_right (e : Ordinal 5)
  : (@Hom Δ) 5 4
  := δ[3; snd (simplex_triangle_product_adjacency e)] ∘
      ((@Cat.Core.id Δ 3) ∘ repeated_shared).

Definition shared_space (e : Ordinal 5)
  : SimplexTriangleProductSpaceF
      (fst (fst (simplex_triangle_product_adjacency e))) ∘ shared_left e ≈
    SimplexTriangleProductSpaceF
      (snd (fst (simplex_triangle_product_adjacency e))) ∘ shared_right e.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  exact (fst (simplex_eq_iff _ _)
    (simplex_triangle_product_adjacent_space e) (repeated_shared z)).
Defined.

Definition shared_time (e : Ordinal 5)
  : SimplexTriangleProductTimeF
      (fst (fst (simplex_triangle_product_adjacency e))) ∘ shared_left e ≈
    SimplexTriangleProductTimeF
      (snd (fst (simplex_triangle_product_adjacency e))) ∘ shared_right e.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  exact (fst (simplex_eq_iff _ _)
    (simplex_triangle_product_adjacent_time e) (repeated_shared z)).
Defined.

Definition shared_factor (e : Ordinal 5)
  := SimplexTriangleProductAdjacentFactor e (shared_left e) (shared_right e)
      (shared_space e) (shared_time e).

Definition six_ranks {m : nat} (f : (@Hom Δ) 5 m)
  : nat * nat * nat * nat * nat * nat
  := (fin_rank (f fin_first), fin_rank (f fin_first⁺),
      fin_rank (f fin_first⁺⁺), fin_rank (f fin_first⁺⁺⁺),
      fin_rank (f fin_first⁺⁺⁺⁺), fin_rank (f fin_first⁺⁺⁺⁺⁺)).

Example all_six_shared_mediators_compute
  : six_results (λ e, six_ranks (shared_factor e).1) =
      ((0,0,1,2,3,3), (0,0,1,2,3,3), (0,0,1,2,3,3),
       (0,0,1,2,3,3), (0,0,1,2,3,3), (0,0,1,2,3,3)).
Proof. vm_compute. reflexivity. Defined.

Example both_reconstructions_compute
  : ∀ e, (six_ranks (δ[3; snd (simplex_triangle_product_adjacency e)] ∘
        (shared_factor e).1), six_ranks (shared_right e)) =
      (six_ranks (shared_left e), six_ranks (shared_left e)).
Proof.
  intros [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]];
    vm_compute; reflexivity.
Defined.

(** ** A Real Product-Presheaf Client

    Evaluate the identity map through the cover and recover both actual
    degree-eight coordinates. No Kan or extension witness is available. *)

(** ** 实际积预层客户端

    通过覆盖求值恒等映射并恢复两个实际八维坐标；不提供 Kan 或延拓见证。 *)

Definition triangle_product
  : Fct (Δ^op) SetCat
  := SimplicialParameterF (Δ[2]) 2.

Definition actual_input
  : triangle_product 8
  := ({|lower := SimplexTriangleProductSpaceF fin_first⁺⁺⁺⁺ ∘ repeated_shape|},
      {|lower := SimplexTriangleProductTimeF fin_first⁺⁺⁺⁺ ∘ repeated_shape|}).

Definition actual_cover_factor
  : ∃ i : Ordinal 5, ∃ h : (@Hom Δ) 8 4,
      triangle_product[h]Δ (simplex_triangle_product_generator i) ≈S actual_input
  := simplex_triangle_product_cover 8 actual_input.

Definition actual_reconstructed
  : triangle_product 8
  := triangle_product[actual_cover_factor.2.1]Δ
      (simplex_triangle_product_generator actual_cover_factor.1).

Example actual_product_reconstruction_computes
  : (nine_ranks (lower (fst actual_reconstructed)),
     nine_ranks (lower (snd actual_reconstructed))) =
      ((0,0,1,1,1,1,2,2,2), (0,0,0,0,1,1,1,1,2)).
Proof. vm_compute. reflexivity. Defined.

Definition actual_identity_factor
  := simplex_triangle_product_eval_factor
      (IdN : triangle_product ⇒ triangle_product)
      (lower (fst actual_input)) (lower (snd actual_input)).

Definition actual_maps_determined
  := snd (simplex_triangle_product_map_eq_iff
      (IdN : triangle_product ⇒ triangle_product) IdN)
      (λ i, reflexivity (simplex_triangle_product_eval
        (IdN : triangle_product ⇒ triangle_product) i)).

Fail Definition no_automatic_Kan
  : HasKanFillers triangle_product
  := _.

(** ** Both Coordinates are Necessary

    On the same staircase, repeated spatial or temporal coordinates
    alone do not determine a position. These are actual point operators,
    not missing-argument failures. *)

(** ** 两个坐标都必要

    同一阶梯中，单独的重复空间或时间坐标不能确定位置。下述使用实际点算子，
    不以缺少参数导致的失败代替反例。 *)

Program Definition grid_point (j : Ordinal 4)
  : (@Hom Δ) 0%nat 4
  := @OrdinalF 0 4 (λ _, j) (λ _ _ _, le_n _).

Example space_alone_does_not_determine_factor
  : (SimplexTriangleProductSpaceF fin_first ∘ grid_point fin_first ≈
      SimplexTriangleProductSpaceF fin_first ∘ grid_point fin_first⁺) ∧
      ¬ (grid_point fin_first ≈ grid_point fin_first⁺).
Proof.
  split.
  - apply (snd (simplex_eq_iff _ _)). intros [[] | []]. reflexivity.
  - intros E. pose proof (fst (simplex_eq_iff _ _) E fin_first) as H.
    discriminate H.
Defined.

Example time_alone_does_not_determine_factor
  : (SimplexTriangleProductTimeF fin_first ∘ grid_point fin_first⁺⁺ ≈
      SimplexTriangleProductTimeF fin_first ∘ grid_point fin_first⁺⁺⁺) ∧
      ¬ (grid_point fin_first⁺⁺ ≈ grid_point fin_first⁺⁺⁺).
Proof.
  split.
  - apply (snd (simplex_eq_iff _ _)). intros [[] | []]. reflexivity.
  - intros E. pose proof (fst (simplex_eq_iff _ _) E fin_first) as H.
    discriminate H.
Defined.
