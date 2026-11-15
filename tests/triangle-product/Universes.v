From Cats Require Import
  Instance.Set.Simplicial.TriangleProduct
  Instance.Set.PresheafDescent.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Triangle Product Covers at Independent Value Sizes *)

(** * 独立取值大小下的三角积覆盖 *)

(** ** Lower Equality

    No Kan selection, extension map or chosen target algebra is available.
    The cover and compatibility clients use the original product presheaf. *)

(** ** 较低相等层级

    不提供 Kan 选择、延拓映射或选定目标代数；覆盖与相容性客户端使用原积预层。 *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Let Q
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := SimplicialParameterF (Δ[2] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 2.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (K L : Q ⇒ X).

Definition lower_cover
  : is_presheaf_cover
      (Q := Q) (simplex_triangle_product_generator@{u l _ _ _ _ _ _ _})
  := simplex_triangle_product_cover.

Definition lower_factor (n : nat) (a b : (@Hom Δ) n 2)
  : K n ({|lower := a|}, {|lower := b|}) ≈S
      X[(SimplexTriangleProductFactor a b).2.1]Δ
        (simplex_triangle_product_eval K (SimplexTriangleProductFactor a b).1)
  := simplex_triangle_product_eval_factor K a b.

Definition lower_determination
  : (K ≈N L) ↔ ∀ i,
      simplex_triangle_product_eval K i ≈S simplex_triangle_product_eval L i
  := simplex_triangle_product_map_eq_iff K L.

Definition lower_compatible
  : presheaf_values_compatible (Q := Q)
      simplex_triangle_product_generator (λ i, simplex_triangle_product_eval K i)
  := presheaf_map_values_compatible simplex_triangle_product_generator K.

End lowerSizes.

(** ** Higher Equality

    No Kan selection, extension map or chosen target algebra is available.
    The cover and compatibility clients use the original product presheaf. *)

(** ** 较高相等层级

    不提供 Kan 选择、延拓映射或选定目标代数；覆盖与相容性客户端使用原积预层。 *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialParameterF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (K L : Q ⇒ X).

Definition higher_cover
  : is_presheaf_cover
      (Q := Q) (simplex_triangle_product_generator@{u p _ _ _ _ _ _ _})
  := simplex_triangle_product_cover.

Definition higher_factor (n : nat) (a b : (@Hom Δ) n 2)
  : K n ({|lower := a|}, {|lower := b|}) ≈S
      X[(SimplexTriangleProductFactor a b).2.1]Δ
        (simplex_triangle_product_eval K (SimplexTriangleProductFactor a b).1)
  := simplex_triangle_product_eval_factor K a b.

Definition higher_determination
  : (K ≈N L) ↔ ∀ i,
      simplex_triangle_product_eval K i ≈S simplex_triangle_product_eval L i
  := simplex_triangle_product_map_eq_iff K L.

Definition higher_compatible
  : presheaf_values_compatible (Q := Q)
      simplex_triangle_product_generator (λ i, simplex_triangle_product_eval K i)
  := presheaf_map_values_compatible simplex_triangle_product_generator K.

End higherSizes.
