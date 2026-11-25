From Cats Require Import
  Instance.Set.Simplicial.PrismOverlap.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Value Bounds for Overlap Witnesses *)

(** * 交叠见证的独立取值界 *)

(** ** Strict Profiles

    Test carrier above and below equality, with no Kan choices or Group.
    The overlap criterion remains Type-valued in both profiles. *)

(** ** 严格配置

    分别检查载体高于与低于相等，无 Kan 选择或群；两种配置的交叠条件均保留
    Type 值见证。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Arbitrary adjacent factors use only a supplied face equation. *)

(** 任意相邻因子只用给定面方程。 *)

Definition lower_adjacent
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (m n : nat)
    (i : Ordinal m) (x y : X (S (S m)))
    (H : d[X; S m; i↑⁺] x ≈S d[X; S m; i↑⁺] y)
    (f g : (@Hom Δ) n (S (S m)))
    (E : σ[S m; i↑] ∘ f ≈ σ[S m; i⁺] ∘ g)
    (F : SimplexPrismTimeF i↑ ∘ f ≈ SimplexPrismTimeF i⁺ ∘ g)
  : X[f]Δ x ≈S X[g]Δ y
  := simplex_prism_adjacent_overlap i x y H f g E F.

(** A given actual cylinder supplies adjacent equations. *)

(** 给定实际柱提供相邻方程。 *)

Definition lower_actual
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (m : nat)
    (K : SimplicialCylinderF
      (Δ[S m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X)
    (i : Ordinal m)
  : d[X; S m; i↑⁺] (simplex_prism_eval K i↑) ≈S
      d[X; S m; i↑⁺] (simplex_prism_eval K i⁺)
  := simplex_prism_values_adjacent K i.

(** The outer pair uses both adjacent equations and an actual middle value. *)

(** 首尾一对使用两个相邻方程及实际中间值。 *)

Definition lower_outer
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (n : nat)
    (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (f g : (@Hom Δ) n 3)
    (E : σ[2; fin_first] ∘ f ≈ σ[2; fin_first⁺⁺] ∘ g)
    (F : SimplexPrismTimeF fin_first ∘ f ≈
      SimplexPrismTimeF fin_first⁺⁺ ∘ g)
  : X[f]Δ (a fin_first) ≈S X[g]Δ (a fin_first⁺⁺)
  := simplex_triangle_prism_outer_overlap a H0 H1 f g E F.

(** Every ordered pair and source degree is covered. *)

(** 覆盖每个有序对及来源维数。 *)

Definition lower_all
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (n : nat)
    (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (i j : Ordinal 2) (f g : (@Hom Δ) n 3)
    (E : σ[2; i] ∘ f ≈ σ[2; j] ∘ g)
    (F : SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g)
  : X[f]Δ (a i) ≈S X[g]Δ (a j)
  := simplex_triangle_prism_overlap a H0 H1 i j f g E F.

(** The exact criterion retains the two supplied equality witnesses. *)

(** 精确条件保留两份给定相等见证。 *)

Definition lower_criterion
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (a : Ordinal 2 → X 3)
  : (∀ n (i j : Ordinal 2) (f g : (@Hom Δ) n 3),
      σ[2; i] ∘ f ≈ σ[2; j] ∘ g →
      SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g →
      X[f]Δ (a i) ≈S X[g]Δ (a j)) ↔
      (d[X; 2; fin_first⁺] (a fin_first) ≈S
        d[X; 2; fin_first⁺] (a fin_first⁺)) ∧
      (d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
        d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  := simplex_triangle_prism_overlap_iff a.

(** Arbitrary adjacent factors use only a supplied face equation. *)

(** 任意相邻因子只用给定面方程。 *)

Definition higher_adjacent
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (m n : nat)
    (i : Ordinal m) (x y : X (S (S m)))
    (H : d[X; S m; i↑⁺] x ≈S d[X; S m; i↑⁺] y)
    (f g : (@Hom Δ) n (S (S m)))
    (E : σ[S m; i↑] ∘ f ≈ σ[S m; i⁺] ∘ g)
    (F : SimplexPrismTimeF i↑ ∘ f ≈ SimplexPrismTimeF i⁺ ∘ g)
  : X[f]Δ x ≈S X[g]Δ y
  := simplex_prism_adjacent_overlap i x y H f g E F.

(** A given actual cylinder supplies adjacent equations. *)

(** 给定实际柱提供相邻方程。 *)

Definition higher_actual
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (m : nat)
    (K : SimplicialCylinderF
      (Δ[S m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
    (i : Ordinal m)
  : d[X; S m; i↑⁺] (simplex_prism_eval K i↑) ≈S
      d[X; S m; i↑⁺] (simplex_prism_eval K i⁺)
  := simplex_prism_values_adjacent K i.

(** The outer pair uses both adjacent equations and an actual middle value. *)

(** 首尾一对使用两个相邻方程及实际中间值。 *)

Definition higher_outer
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
    (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (f g : (@Hom Δ) n 3)
    (E : σ[2; fin_first] ∘ f ≈ σ[2; fin_first⁺⁺] ∘ g)
    (F : SimplexPrismTimeF fin_first ∘ f ≈
      SimplexPrismTimeF fin_first⁺⁺ ∘ g)
  : X[f]Δ (a fin_first) ≈S X[g]Δ (a fin_first⁺⁺)
  := simplex_triangle_prism_outer_overlap a H0 H1 f g E F.

(** Every ordered pair and source degree is covered. *)

(** 覆盖每个有序对及来源维数。 *)

Definition higher_all
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
    (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (i j : Ordinal 2) (f g : (@Hom Δ) n 3)
    (E : σ[2; i] ∘ f ≈ σ[2; j] ∘ g)
    (F : SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g)
  : X[f]Δ (a i) ≈S X[g]Δ (a j)
  := simplex_triangle_prism_overlap a H0 H1 i j f g E F.

(** The exact criterion retains the two supplied equality witnesses. *)

(** 精确条件保留两份给定相等见证。 *)

Definition higher_criterion
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (a : Ordinal 2 → X 3)
  : (∀ n (i j : Ordinal 2) (f g : (@Hom Δ) n 3),
      σ[2; i] ∘ f ≈ σ[2; j] ∘ g →
      SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g →
      X[f]Δ (a i) ≈S X[g]Δ (a j)) ↔
      (d[X; 2; fin_first⁺] (a fin_first) ≈S
        d[X; 2; fin_first⁺] (a fin_first⁺)) ∧
      (d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
        d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  := simplex_triangle_prism_overlap_iff a.

End StrictSizes.
