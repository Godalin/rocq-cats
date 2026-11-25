From Cats Require Import
  Instance.Set.Simplicial.PrismGluing.
From Cats.Set Require Import
  Pi
  Subset.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Gluing at Independent Carrier and Equality Levels *)

(** * 独立载体与相等层级下的粘合 *)

(** ** lower Equality Profile

    Fix strictly separated levels. The actual product source and target
    share ambient bounds; no Kan or algebra selection is present. *)

(** ** lower 相等配置

    固定严格分离的层级；实际积来源与目标共用环境界，无 Kan 或代数选择。 *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Context {X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}}.

(** The source is the actual product cylinder, not a generated sieve. *)

(** 来源是实际积柱，而非生成筛。 *)

Definition lower_cover (m : nat)
  : is_presheaf_cover
      (Q := SimplicialCylinderF
        (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}))
      (simplex_prism_generator m)
  := simplex_prism_cover m.

(** Both coordinate equations are retained in the compatibility criterion. *)

(** 相容判据保留两个坐标方程。 *)

Definition lower_compatible (m : nat) (a : Ordinal m → X (S m))
  : presheaf_values_compatible (simplex_prism_generator m) a ↔
      (∀ n (i j : Ordinal m) (f g : (@Hom Δ) n (S m)),
        σ[m; i] ∘ f ≈ σ[m; j] ∘ g →
        SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g →
        X[f]Δ (a i) ≈S X[g]Δ (a j))
  := simplex_prism_compatible_iff a.

(** Transparent construction requires only compatible values. *)

(** 透明构造只要求值相容。 *)

Definition lower_map (m : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
  : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X
  := SimplexPrismGluingN a H.

(** Recovery retains the target's specified equality. *)

(** 恢复保留目标的指定相等。 *)

Definition lower_β (m : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a) i
  : simplex_prism_eval (lower_map m a H) i ≈S a i
  := simplex_prism_gluing_β a H i.

(** Any valid two-coordinate factor may compute the value. *)

(** 任意有效的双坐标因子都可计算该值。 *)

Definition lower_factor (m n : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
    (s : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
    (i : Ordinal m) (h : (@Hom Δ) n (S m))
    (E : σ[m; i] ∘ h ≈ s) (F : SimplexPrismTimeF i ∘ h ≈ t)
  : lower_map m a H n ({|lower := s|}, {|lower := t|}) ≈S X[h]Δ (a i)
  := simplex_prism_gluing_factor a H s t i h E F.

(** The actual chosen raw value is the interleaved restriction. *)

(** 实际所选原始值就是交织限制。 *)

Definition lower_computation (m n : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
    (s : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : lower_map m a H n ({|lower := s|}, {|lower := t|}) =
      X[SimplexPrismIndexF s t]Δ (a (simplex_prism_pivot s t))
  := eq_refl.

(** The full extension property is Type-valued. *)

(** 完整延拓泛性质保留 Type 值。 *)

Definition lower_universal (m : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
  : is_unique (R := @NatEq _ _ _ _)
      (λ K : SimplicialCylinderF
        (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X,
        ∀ i, simplex_prism_eval K i ≈S a i) (lower_map m a H)
  := simplex_prism_gluing_universal a H.

(** Reconstructing a map uses its own natural compatibility. *)

(** 重构映射使用其自身自然给出的相容条件。 *)

Definition lower_η (m : nat) (K : SimplicialCylinderF
    (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X)
  : SimplexPrismGluingN (λ i, simplex_prism_eval K i)
      (simplex_prism_values_compatible K) ≈N K
  := simplex_prism_gluing_η K.

(** The packaged map compares values, not compatibility records. *)

(** 打包映射比较值，而不比较相容记录。 *)

Definition lower_resp (m : nat)
  : SubsetS (PiS (Ordinal m) (λ _, X (S m)))
      (presheaf_values_compatible (simplex_prism_generator m)) →r
      Nat_SetS (SimplicialCylinderF
        (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _})) X
  := simplex_prism_gluing_resp.

(** The two triangle equations suffice for actual gluing. *)

(** 两条三角柱方程足以进行实际粘合。 *)

Definition lower_triangle (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  : SimplicialCylinderF
      (Δ[2] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X
  := SimplexTrianglePrismGluingN a H0 H1.

(** Necessity and sufficiency retain the actual map in the witness. *)

(** 充要条件在见证中保留实际映射。 *)

Definition lower_existence (a : Ordinal 2 → X 3)
  : (∃ K : SimplicialCylinderF
        (Δ[2] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X,
        ∀ i, simplex_prism_eval K i ≈S a i) ↔
      (d[X; 2; fin_first⁺] (a fin_first) ≈S
        d[X; 2; fin_first⁺] (a fin_first⁺)) ∧
      (d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
        d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  := simplex_triangle_prism_gluing_iff a.

(** Triangle reconstruction does not compare derived equation witnesses. *)

(** 三角柱重构不比较导出方程的见证。 *)

Definition lower_triangle_η (K : SimplicialCylinderF
    (Δ[2] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X)
  : SimplexTrianglePrismGluingN (λ i, simplex_prism_eval K i)
      (simplex_prism_values_adjacent K fin_first)
      (simplex_prism_values_adjacent K fin_first⁺) ≈N K
  := simplex_triangle_prism_gluing_η K.

End lowerSizes.

(** ** higher Equality Profile

    Fix strictly separated levels. The actual product source and target
    share ambient bounds; no Kan or algebra selection is present. *)

(** ** higher 相等配置

    固定严格分离的层级；实际积来源与目标共用环境界，无 Kan 或代数选择。 *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.

(** The source is the actual product cylinder, not a generated sieve. *)

(** 来源是实际积柱，而非生成筛。 *)

Definition higher_cover (m : nat)
  : is_presheaf_cover
      (Q := SimplicialCylinderF
        (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}))
      (simplex_prism_generator m)
  := simplex_prism_cover m.

(** Both coordinate equations are retained in the compatibility criterion. *)

(** 相容判据保留两个坐标方程。 *)

Definition higher_compatible (m : nat) (a : Ordinal m → X (S m))
  : presheaf_values_compatible (simplex_prism_generator m) a ↔
      (∀ n (i j : Ordinal m) (f g : (@Hom Δ) n (S m)),
        σ[m; i] ∘ f ≈ σ[m; j] ∘ g →
        SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g →
        X[f]Δ (a i) ≈S X[g]Δ (a j))
  := simplex_prism_compatible_iff a.

(** Transparent construction requires only compatible values. *)

(** 透明构造只要求值相容。 *)

Definition higher_map (m : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
  : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X
  := SimplexPrismGluingN a H.

(** Recovery retains the target's specified equality. *)

(** 恢复保留目标的指定相等。 *)

Definition higher_β (m : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a) i
  : simplex_prism_eval (higher_map m a H) i ≈S a i
  := simplex_prism_gluing_β a H i.

(** Any valid two-coordinate factor may compute the value. *)

(** 任意有效的双坐标因子都可计算该值。 *)

Definition higher_factor (m n : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
    (s : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
    (i : Ordinal m) (h : (@Hom Δ) n (S m))
    (E : σ[m; i] ∘ h ≈ s) (F : SimplexPrismTimeF i ∘ h ≈ t)
  : higher_map m a H n ({|lower := s|}, {|lower := t|}) ≈S X[h]Δ (a i)
  := simplex_prism_gluing_factor a H s t i h E F.

(** The actual chosen raw value is the interleaved restriction. *)

(** 实际所选原始值就是交织限制。 *)

Definition higher_computation (m n : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
    (s : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : higher_map m a H n ({|lower := s|}, {|lower := t|}) =
      X[SimplexPrismIndexF s t]Δ (a (simplex_prism_pivot s t))
  := eq_refl.

(** The full extension property is Type-valued. *)

(** 完整延拓泛性质保留 Type 值。 *)

Definition higher_universal (m : nat) (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible (simplex_prism_generator m) a)
  : is_unique (R := @NatEq _ _ _ _)
      (λ K : SimplicialCylinderF
        (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
        ∀ i, simplex_prism_eval K i ≈S a i) (higher_map m a H)
  := simplex_prism_gluing_universal a H.

(** Reconstructing a map uses its own natural compatibility. *)

(** 重构映射使用其自身自然给出的相容条件。 *)

Definition higher_η (m : nat) (K : SimplicialCylinderF
    (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
  : SimplexPrismGluingN (λ i, simplex_prism_eval K i)
      (simplex_prism_values_compatible K) ≈N K
  := simplex_prism_gluing_η K.

(** The packaged map compares values, not compatibility records. *)

(** 打包映射比较值，而不比较相容记录。 *)

Definition higher_resp (m : nat)
  : SubsetS (PiS (Ordinal m) (λ _, X (S m)))
      (presheaf_values_compatible (simplex_prism_generator m)) →r
      Nat_SetS (SimplicialCylinderF
        (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _})) X
  := simplex_prism_gluing_resp.

(** The two triangle equations suffice for actual gluing. *)

(** 两条三角柱方程足以进行实际粘合。 *)

Definition higher_triangle (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  : SimplicialCylinderF
      (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X
  := SimplexTrianglePrismGluingN a H0 H1.

(** Necessity and sufficiency retain the actual map in the witness. *)

(** 充要条件在见证中保留实际映射。 *)

Definition higher_existence (a : Ordinal 2 → X 3)
  : (∃ K : SimplicialCylinderF
        (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
        ∀ i, simplex_prism_eval K i ≈S a i) ↔
      (d[X; 2; fin_first⁺] (a fin_first) ≈S
        d[X; 2; fin_first⁺] (a fin_first⁺)) ∧
      (d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
        d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  := simplex_triangle_prism_gluing_iff a.

(** Triangle reconstruction does not compare derived equation witnesses. *)

(** 三角柱重构不比较导出方程的见证。 *)

Definition higher_triangle_η (K : SimplicialCylinderF
    (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
  : SimplexTrianglePrismGluingN (λ i, simplex_prism_eval K i)
      (simplex_prism_values_adjacent K fin_first)
      (simplex_prism_values_adjacent K fin_first⁺) ≈N K
  := simplex_triangle_prism_gluing_η K.

End higherSizes.
