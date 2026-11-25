From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereTriangle.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Strict Sizes for Conditional Triangle Extensions *)

(** * 条件三角延拓的严格大小 *)

(** ** Lower Equality Bounds

    Fix independent sizes and arbitrary sources/targets, with no Kan or
    algebra choices. The actual extension remains an explicit input. *)

(** ** 较低相等界

    固定独立大小及任意源／目标，无 Kan 或代数选择；实际延拓保持为显式输入。 *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Context (A B X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).
Context (i : B ⇒ A) (c : B ⇒ X).
Context (T : SimplicialParameterF A 2 ⇒ X).

Definition lower_endpoint (j : Ordinal 2) (t : bool)
  := simplicial_triangle_edge_endpoint T j t.

Definition lower_composite (f g h : A ⇒ X)
    (H : SimplicialHomotopy f g) (K : SimplicialHomotopy g h)
    (E01 : simplicial_triangle_edge T fin_first⁺⁺ ≈N homotopy_map H)
    (E12 : simplicial_triangle_edge T fin_first ≈N homotopy_map K)
  : SimplicialHomotopy f h
  := SimplicialTriangleComposite T H K E01 E12.

Definition lower_reverse (f g : A ⇒ X) (H : SimplicialHomotopy f g)
    (E01 : simplicial_triangle_edge T fin_first⁺⁺ ≈N homotopy_map H)
    (E02 : simplicial_triangle_edge T fin_first⁺ ≈N
      homotopy_map (SimplicialConstantHomotopy f))
  : SimplicialHomotopy g f
  := SimplicialTriangleReverse T H E01 E02.

Definition lower_restrict (R : is_simplicial_parameter_relative i c T)
    (j : Ordinal 2)
  : is_simplicial_parameter_relative i c (simplicial_triangle_edge T j)
  := simplicial_parameter_restrict_relative i c T R δ[1; j].

Definition lower_relative_proper (T' : SimplicialParameterF A 2 ⇒ X) (E : T ≈N T')
  : is_simplicial_parameter_relative i c T ↔
      is_simplicial_parameter_relative i c T'
  := simplicial_parameter_relative_proper i c T T' E.

Definition lower_map_proper (T' : SimplicialParameterF A 2 ⇒ X) (E : T ≈N T')
    (j : Ordinal 2)
  : simplicial_triangle_edge T j ≈N simplicial_triangle_edge T' j
  := simplicial_triangle_edge_proper T T' E j.

Context (b : X 0) (S : SimplicialParameterF (Δ[2]) 2 ⇒ X)
    (R : is_two_sphere_triangle_relative X b S).

Definition lower_sphere_composite (x y z : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
    (K : TwoSphereCylinderHomotopy X b y z)
    (E01 : simplicial_triangle_edge S fin_first⁺⁺ ≈N homotopy_map H.1)
    (E12 : simplicial_triangle_edge S fin_first ≈N homotopy_map K.1)
  : TwoSphereCylinderHomotopy X b x z
  := SphereTriangleComposite X b S R H K E01 E12.

Definition lower_sphere_reverse (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
    (E01 : simplicial_triangle_edge S fin_first⁺⁺ ≈N homotopy_map H.1)
    (E02 : simplicial_triangle_edge S fin_first⁺ ≈N
      homotopy_map (SimplicialConstantHomotopy ⟦x.1⟧Δ[X; 2]))
  : TwoSphereCylinderHomotopy X b y x
  := SphereTriangleReverse X b S R H E01 E02.

End lowerSizes.

(** ** Higher Equality Bounds

    Fix independent sizes and arbitrary sources/targets, with no Kan or
    algebra choices. The actual extension remains an explicit input. *)

(** ** 较高相等界

    固定独立大小及任意源／目标，无 Kan 或代数选择；实际延拓保持为显式输入。 *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Context (A B X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (i : B ⇒ A) (c : B ⇒ X).
Context (T : SimplicialParameterF A 2 ⇒ X).

Definition higher_endpoint (j : Ordinal 2) (t : bool)
  := simplicial_triangle_edge_endpoint T j t.

Definition higher_composite (f g h : A ⇒ X)
    (H : SimplicialHomotopy f g) (K : SimplicialHomotopy g h)
    (E01 : simplicial_triangle_edge T fin_first⁺⁺ ≈N homotopy_map H)
    (E12 : simplicial_triangle_edge T fin_first ≈N homotopy_map K)
  : SimplicialHomotopy f h
  := SimplicialTriangleComposite T H K E01 E12.

Definition higher_reverse (f g : A ⇒ X) (H : SimplicialHomotopy f g)
    (E01 : simplicial_triangle_edge T fin_first⁺⁺ ≈N homotopy_map H)
    (E02 : simplicial_triangle_edge T fin_first⁺ ≈N
      homotopy_map (SimplicialConstantHomotopy f))
  : SimplicialHomotopy g f
  := SimplicialTriangleReverse T H E01 E02.

Definition higher_restrict (R : is_simplicial_parameter_relative i c T)
    (j : Ordinal 2)
  : is_simplicial_parameter_relative i c (simplicial_triangle_edge T j)
  := simplicial_parameter_restrict_relative i c T R δ[1; j].

Definition higher_relative_proper (T' : SimplicialParameterF A 2 ⇒ X) (E : T ≈N T')
  : is_simplicial_parameter_relative i c T ↔
      is_simplicial_parameter_relative i c T'
  := simplicial_parameter_relative_proper i c T T' E.

Definition higher_map_proper (T' : SimplicialParameterF A 2 ⇒ X) (E : T ≈N T')
    (j : Ordinal 2)
  : simplicial_triangle_edge T j ≈N simplicial_triangle_edge T' j
  := simplicial_triangle_edge_proper T T' E j.

Context (b : X 0) (S : SimplicialParameterF (Δ[2]) 2 ⇒ X)
    (R : is_two_sphere_triangle_relative X b S).

Definition higher_sphere_composite (x y z : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
    (K : TwoSphereCylinderHomotopy X b y z)
    (E01 : simplicial_triangle_edge S fin_first⁺⁺ ≈N homotopy_map H.1)
    (E12 : simplicial_triangle_edge S fin_first ≈N homotopy_map K.1)
  : TwoSphereCylinderHomotopy X b x z
  := SphereTriangleComposite X b S R H K E01 E12.

Definition higher_sphere_reverse (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
    (E01 : simplicial_triangle_edge S fin_first⁺⁺ ≈N homotopy_map H.1)
    (E02 : simplicial_triangle_edge S fin_first⁺ ≈N
      homotopy_map (SimplicialConstantHomotopy ⟦x.1⟧Δ[X; 2]))
  : TwoSphereCylinderHomotopy X b y x
  := SphereTriangleReverse X b S R H E01 E02.

End higherSizes.

(** Importing the parameter theory does not select model products. *)

(** 导入参数理论不选定模型的积结构。 *)

Fail Definition unchosen_set_product
  : HasProduct SetCat
  := _.

Fail Definition unchosen_simplicial_product
  : HasProduct (SimplicialCat : Cat)
  := _.
