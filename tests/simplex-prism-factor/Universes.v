From Cats Require Import
  Instance.Set.Simplicial.Prism
  Instance.Set.Simplicial.Homotopy.SphereCylinder.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Cylinder Values at Independent Sizes *)

(** * 独立大小下的柱取值 *)

(** ** Strict Profiles

    Keep both strict carrier/equality orders. None of the map or sphere
    clients has Kan choices, algebra structures or equality of functions. *)

(** ** 严格配置

    保留两种严格载体／相等次序。所有映射及球面客户端均不要求 Kan 选择、
    代数结构或函数相等。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The all-degree factor law only requires a given cylinder map. *)

(** 逐维分解律只需给定柱映射。 *)

Definition lower_factor
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (m n : nat)
    (K : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X)
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : K n ({|lower := a|}, {|lower := t|}) ≈S
      X[SimplexPrismIndexF a t]Δ
        (simplex_prism_eval K (simplex_prism_pivot a t))
  := simplex_prism_eval_factor K a t.

(** Staircase values determine equality in every degree. *)

(** 阶梯值确定每一维中的相等。 *)

Definition lower_maps
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (m : nat)
    (K L : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X)
  : (K ≈N L) ↔ ∀ k, simplex_prism_eval K k ≈S simplex_prism_eval L k
  := simplex_prism_map_eq_iff K L.

(** The existing actual sphere prism table is consumed unchanged. *)

(** 既有实际球面棱柱表保持不变而被消费。 *)

Definition lower_sphere
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (n : nat) (a : (@Hom Δ) n 2) (t : (@Hom Δ) n 1%nat)
  : two_sphere_cylinder_eval X b H a t ≈S
      X[SimplexPrismIndexF a t]Δ
        (two_sphere_prism H (simplex_prism_pivot a t))
  := two_sphere_cylinder_factor H a t.

(** The all-degree factor law only requires a given cylinder map. *)

(** 逐维分解律只需给定柱映射。 *)

Definition higher_factor
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (m n : nat)
    (K : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : K n ({|lower := a|}, {|lower := t|}) ≈S
      X[SimplexPrismIndexF a t]Δ
        (simplex_prism_eval K (simplex_prism_pivot a t))
  := simplex_prism_eval_factor K a t.

(** Staircase values determine equality in every degree. *)

(** 阶梯值确定每一维中的相等。 *)

Definition higher_maps
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (m : nat)
    (K L : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
  : (K ≈N L) ↔ ∀ k, simplex_prism_eval K k ≈S simplex_prism_eval L k
  := simplex_prism_map_eq_iff K L.

(** The existing actual sphere prism table is consumed unchanged. *)

(** 既有实际球面棱柱表保持不变而被消费。 *)

Definition higher_sphere
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (n : nat) (a : (@Hom Δ) n 2) (t : (@Hom Δ) n 1%nat)
  : two_sphere_cylinder_eval X b H a t ≈S
      X[SimplexPrismIndexF a t]Δ
        (two_sphere_prism H (simplex_prism_pivot a t))
  := two_sphere_cylinder_factor H a t.

End StrictSizes.
