From Cats Require Import
  Instance.Set.Simplicial.PrismGluing
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Gluing Native-Distinct Values and Witnesses

    Boolean equality witnesses identify native-distinct values. Two
    adjacent witnesses are supplied directly, without a prior cylinder
    map, Kan structure, or coefficient classification. *)

(** * 粘合原生不同的值与见证

    布尔相等见证认同原生不同的值。直接给定两个相邻见证，无预先已有的柱
    映射、Kan 结构或系数分类。 *)

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

Definition supplied (i : Ordinal 2)
  : W 3
  := Nat.eqb (fin_rank i) 1.

Definition glued
  : SimplicialCylinderF (Δ[2]) ⇒ W
  := SimplexTrianglePrismGluingN supplied false true.

Definition other_glued
  : SimplicialCylinderF (Δ[2]) ⇒ W
  := SimplexTrianglePrismGluingN supplied true false.

Example supplied_values_recovered_compute
  : (simplex_prism_eval glued fin_first,
     simplex_prism_eval glued fin_first⁺,
     simplex_prism_eval glued fin_first⁺⁺) = (false, true, false).
Proof. vm_compute. reflexivity. Defined.

Definition repeated_space
  : (@Hom Δ) 5 2
  := σ[2; fin_first] ∘
      (σ[3; fin_first⁺⁺] ∘ σ[4; fin_first⁺⁺⁺⁺]).

Definition repeated_time
  : (@Hom Δ) 5 1%nat
  := SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4).

Definition first_position
  : (@Hom Δ) 0%nat 5
  := ConstF [Ord 0] (C := [Ord 5]) fin_first.

(** The pivot changes on restriction; the actual map remains natural in
    specified equality, without native equality of the chosen values. *)

(** 限制会改变枢轴；实际映射按指定相等仍自然，不要求所选值原生相等。 *)

Example high_degenerate_values_compute
  : (glued 5 ({|lower := repeated_space|}, {|lower := repeated_time|}),
     glued 0 ({|lower := repeated_space ∘ first_position|},
              {|lower := repeated_time ∘ first_position|})) = (true, false).
Proof. vm_compute. reflexivity. Defined.

Definition restriction_is_natural
  := nat_naturality glued first_position
      ({|lower := repeated_space|}, {|lower := repeated_time|}).

Definition independent_equation_witnesses
  : glued ≈N other_glued
  := simplex_triangle_prism_gluing_proper supplied supplied
      false true true false (λ i, true).

Definition bundled_gluing_proper
  : simplex_prism_gluing_resp
      (supplied; simplex_triangle_prism_values_compatible supplied false true)
      ≈N simplex_prism_gluing_resp
        (supplied; simplex_triangle_prism_values_compatible supplied true false).
Proof.
  apply (@func_proper _ _ simplex_prism_gluing_resp).
  intros i. exact true.
Defined.

Definition recovered_equations
  := fst (simplex_triangle_prism_gluing_iff supplied)
      (glued; simplex_triangle_prism_gluing_β supplied false true).

Definition unique_gluing
  := simplex_triangle_prism_gluing_universal supplied false true.

Fail Definition recovered_values_are_native_equal
  : simplex_prism_eval glued fin_first = simplex_prism_eval glued fin_first⁺
  := eq_refl.

Fail Definition restriction_is_native_equality
  : glued 5 ({|lower := repeated_space|}, {|lower := repeated_time|}) =
      glued 0 ({|lower := repeated_space ∘ first_position|},
               {|lower := repeated_time ∘ first_position|})
  := eq_refl.

(** An all-one time coordinate uses default pivot zero. Another valid
    pivot may compute a native-distinct but specified-equal value. *)

(** 时间恒为一时使用默认枢轴零；另一有效枢轴可算出原生不同但指定相等的值。 *)

Definition all_one_space
  : (@Hom Δ) 0%nat 2
  := ConstF [Ord 0] (C := [Ord 2]) fin_first⁺⁺.

Definition all_one_time
  : (@Hom Δ) 0%nat 1%nat
  := ConstF [Ord 0] (C := [Ord 1]) fin_first⁺.

Definition another_factor
  : (@Hom Δ) 0%nat 3
  := ConstF [Ord 0] (C := [Ord 3]) fin_first⁺⁺⁺.

Definition another_space_equation
  : σ[2; fin_first⁺] ∘ another_factor ≈ all_one_space.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros [[] | []]. reflexivity.
Defined.

Definition another_time_equation
  : SimplexPrismTimeF fin_first⁺ ∘ another_factor ≈ all_one_time.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros [[] | []]. reflexivity.
Defined.

Definition another_factor_value
  := simplex_prism_gluing_factor supplied
      (simplex_triangle_prism_values_compatible supplied false true)
      all_one_space all_one_time fin_first⁺ another_factor
      another_space_equation another_time_equation.

Example different_valid_pivots_compute
  : (fin_rank (simplex_prism_pivot all_one_space all_one_time),
     glued 0 ({|lower := all_one_space|}, {|lower := all_one_time|}),
     W[another_factor]Δ (supplied fin_first⁺)) = (0, false, true).
Proof. vm_compute. reflexivity. Defined.

(** ** Reconstructing the Actual Product

    The target itself is the product presheaf. Glue its generator values
    and inspect both coordinates of a genuine degree-five datum. *)

(** ** 重构实际积

    目标本身是积预层。粘合其生成元值，并检查真实五维数据的两个坐标。 *)

Definition Q
  : Fct (Δ^op) SetCat
  := SimplicialCylinderF (Δ[2]).

Definition identity_values
  : Ordinal 2 → Q 3
  := simplex_prism_eval (IdN : Q ⇒ Q).

Definition product_glued
  : Q ⇒ Q
  := SimplexTrianglePrismGluingN identity_values
      (simplex_prism_values_adjacent (IdN : Q ⇒ Q) fin_first)
      (simplex_prism_values_adjacent (IdN : Q ⇒ Q) fin_first⁺).

Definition six_ranks {m : nat} (f : (@Hom Δ) 5 m)
  : nat * nat * nat * nat * nat * nat
  := (fin_rank (f fin_first), fin_rank (f fin_first⁺),
      fin_rank (f fin_first⁺⁺), fin_rank (f fin_first⁺⁺⁺),
      fin_rank (f fin_first⁺⁺⁺⁺), fin_rank (f fin_first⁺⁺⁺⁺⁺)).

Example actual_product_reconstructed_compute
  : let z := product_glued 5
      ({|lower := repeated_space|}, {|lower := repeated_time|}) in
    (six_ranks (lower (fst z)), six_ranks (lower (snd z))) =
      ((0, 0, 1, 1, 2, 2), (0, 0, 0, 1, 1, 1)).
Proof. vm_compute. reflexivity. Defined.

Definition product_reconstructed
  : product_glued ≈N (IdN : Q ⇒ Q)
  := simplex_triangle_prism_gluing_η (IdN : Q ⇒ Q).

(** A zero-dimensional spatial source has just one staircase. *)

(** 零维空间来源只有一块阶梯。 *)

Definition Q0
  : Fct (Δ^op) SetCat
  := SimplicialCylinderF (Δ[0]).

Definition point_product_glued
  : Q0 ⇒ Q0
  := SimplexPrismGluingN (simplex_prism_eval (IdN : Q0 ⇒ Q0))
      (simplex_prism_values_compatible (IdN : Q0 ⇒ Q0)).

Example point_cylinder_reconstructed_compute
  : let z := point_product_glued 1
      ({|lower := ConstF [Ord 1] (C := [Ord 0]) fin_first|},
       {|lower := (id : (@Hom Δ) 1%nat 1%nat)|}) in
    (fin_rank (lower (fst z) fin_first),
     fin_rank (lower (snd z) fin_first),
     fin_rank (lower (snd z) fin_first⁺)) = (0, 0, 1).
Proof. vm_compute. reflexivity. Defined.

(** ** Actual Nonzero Cocycle Data Without Kan

    Supply the three degeneracies of the nonzero triangle. The existing
    face/degeneracy laws supply the two equations, so gluing uses no filler.
    Inspect the actual face coefficients, not equality proof fields. *)

(** ** 无 Kan 的实际非零 Cocycle 数据

    给定非零三角形的三个退化；由既有面／退化律提供两个方程，粘合不使用
    填充。检查实际面系数，不检查相等证明字段。 *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_horn
  : HasHornFillers BoolCocycleModel 4 fin_first
  := _.


Definition coefficient_triangle
  : BoolCocycleModel 2
  := (cocycle_two_sphere_resp (M := BoolS_Monoid) true).1.

Definition coefficient_values (i : Ordinal 2)
  : BoolCocycleModel 3
  := s[BoolCocycleModel; 2; i] coefficient_triangle.

Definition coefficient_adjacent (i : Ordinal 1)
  : d[BoolCocycleModel; 2; i↑⁺] (coefficient_values i↑) ≈S
      d[BoolCocycleModel; 2; i↑⁺] (coefficient_values i⁺).
Proof.
  transitivity coefficient_triangle.
  - exact (simplex_face_degeneracy_next i↑ coefficient_triangle).
  - symmetry. exact (simplex_face_degeneracy_id i⁺ coefficient_triangle).
Defined.

Definition coefficient_glued
  : SimplicialCylinderF (Δ[2]) ⇒ BoolCocycleModel
  := SimplexTrianglePrismGluingN coefficient_values
      (coefficient_adjacent fin_first) (coefficient_adjacent fin_first⁺).

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (d[BoolCocycleModel; 2; fin_first] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example coefficient_tetrahedra_compute
  : (face_values (simplex_prism_eval coefficient_glued fin_first),
     face_values (simplex_prism_eval coefficient_glued fin_first⁺),
     face_values (simplex_prism_eval coefficient_glued fin_first⁺⁺)) =
      ((true, true, false, false), (false, true, true, false),
       (false, false, true, true)).
Proof. vm_compute. reflexivity. Defined.

(** ** One Adjacent Equation Cannot Supply the Other

    A constant native-equality target makes the missing condition visible.
    Values false,false,true satisfy the first equation but cannot extend. *)

(** ** 一个相邻方程不能提供另一个

    取原生相等的常目标使遗漏条件可见。假、假、真满足第一个方程，却不能延拓。 *)

Definition B
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) BoolS.

Definition incomplete_values (i : Ordinal 2)
  : B 3
  := Nat.eqb (fin_rank i) 2.

Definition first_equation_alone
  : d[B; 2; fin_first⁺] (incomplete_values fin_first) ≈S
      d[B; 2; fin_first⁺] (incomplete_values fin_first⁺)
  := eq_refl.

Example no_extension_from_first_equation_alone
  : ¬ (∃ K : SimplicialCylinderF (Δ[2]) ⇒ B,
      ∀ i, simplex_prism_eval K i ≈S incomplete_values i).
Proof.
  intros H. destruct (fst (simplex_triangle_prism_gluing_iff incomplete_values) H)
    as [_ E]. discriminate E.
Defined.

(** The symmetric counterexample retains only the second equation. *)

(** 对称反例只保留第二个方程。 *)

Definition incomplete_first_values (i : Ordinal 2)
  : B 3
  := Nat.eqb (fin_rank i) 0.

Definition second_equation_alone
  : d[B; 2; fin_first⁺⁺] (incomplete_first_values fin_first⁺) ≈S
      d[B; 2; fin_first⁺⁺] (incomplete_first_values fin_first⁺⁺)
  := eq_refl.

Example no_extension_from_second_equation_alone
  : ¬ (∃ K : SimplicialCylinderF (Δ[2]) ⇒ B,
      ∀ i, simplex_prism_eval K i ≈S incomplete_first_values i).
Proof.
  intros H.
  destruct (fst (simplex_triangle_prism_gluing_iff incomplete_first_values) H)
    as [E _]. discriminate E.
Defined.
