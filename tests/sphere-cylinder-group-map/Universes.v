From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroupMap.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_map_resp.

(** * Native Sizes and the Weakest Map-Law Interfaces

    Test both strict ambient carrier/equality orders, independent
    presentation choices and the complete original map-law interfaces.
    Unit/identity/composition need no algebra; other laws state only their
    own minimal hypotheses. *)

(** * 原生大小与最弱映射定律接口

    检查两种严格环境载体／相等次序、独立呈现选择及完整原映射定律接口。
    单位／恒等／复合不需代数，其余定律只给出自身的最小前提。 *)

(** ** Lower Equality Bound

    Fix three simplicial objects, two maps and all six presentation
    families; no algebra or full Kan structure is available initially. *)

(** ** 较低相等界

    固定三个单纯对象、两个映射及六份呈现族；初始不提供代数或完整 Kan 结构。 *)

Section Lower.
Universes l u p.
Constraint l < u, u < p.
Context (X Y Z : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).
Context (α : X ⇒ Y) (β : Y ⇒ Z) (b : X 0).
Context (KRX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRZ : ∀ s, HasHornFillers Z
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCZ : ∀ s, HasHornFillers Z
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

Let CX
  : SetC
  := TwoSphereCylinderS X b KRX KCX.

Let CY
  : SetC
  := TwoSphereCylinderS Y (α 0 b) KRY KCY.

(** The unit law needs no selected algebra. *)

(** 单位律不要求选定代数。 *)

Definition lower_unit
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY
        (two_sphere_base X b)) (two_sphere_base Y (α 0 b))
  := two_sphere_cylinder_map_unit α b KRX KCX KRY KCY.

(** Retain the complete exported identity interface at these strict sizes. *)

(** 在这些严格大小处保留完整导出恒等接口。 *)

Definition lower_identity
  := two_sphere_cylinder_map_id X b KRX KCX.

(** Retain the complete composition interface, including independent
    intermediate choices, without re-expanding its dependent endpoints. *)

(** 保留含独立中间选择的完整复合接口，不重新展开其依赖端点。 *)

Definition lower_composition
  := two_sphere_cylinder_map_comp KRX KCX KRY KCY KRZ KCZ α β b.

(** Product preservation needs only target missing-face-two comparison,
    with no source four-dimensional choice or group. *)

(** 乘法保持只需目标缺第二面比较，无须来源四维选择或群。 *)

Definition lower_minimal_product
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺) (x y : CX)
  := two_sphere_cylinder_map_mul α b KRX KCX KRY KCY H K x y.

(** A source left choice suffices to map inverses into a target group. *)

(** 来源左选择已足以将逆映到目标群。 *)

Definition lower_minimal_inverse
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}
    `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺) (x : CX)
  := two_sphere_cylinder_map_left_inverse α b KRX KCX KRY KCY I H K L x.

(** Importing map laws does not select algebraic models or raw equivalence. *)

(** 导入映射定律不选择代数模型或原始等价。 *)

Fail Definition lower_no_group_source : HasMagma CX
  := ltac:(typeclasses eauto).
Fail Definition lower_no_group_target : HasMagma CY
  := ltac:(typeclasses eauto).
Fail Definition lower_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition lower_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Y (α 0 b))
  := ltac:(typeclasses eauto).

End Lower.

(** ** Higher Equality Bound

    Fix three simplicial objects, two maps and all six presentation
    families; no algebra or full Kan structure is available initially. *)

(** ** 较高相等界

    固定三个单纯对象、两个映射及六份呈现族；初始不提供代数或完整 Kan 结构。 *)

Section Higher.
Universes l u p.
Constraint l < u, u < p.
Context (X Y Z : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (α : X ⇒ Y) (β : Y ⇒ Z) (b : X 0).
Context (KRX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRZ : ∀ s, HasHornFillers Z
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCZ : ∀ s, HasHornFillers Z
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

Let CX
  : SetC
  := TwoSphereCylinderS X b KRX KCX.

Let CY
  : SetC
  := TwoSphereCylinderS Y (α 0 b) KRY KCY.

(** The unit law needs no selected algebra. *)

(** 单位律不要求选定代数。 *)

Definition higher_unit
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY
        (two_sphere_base X b)) (two_sphere_base Y (α 0 b))
  := two_sphere_cylinder_map_unit α b KRX KCX KRY KCY.

(** Retain the complete exported identity interface at these strict sizes. *)

(** 在这些严格大小处保留完整导出恒等接口。 *)

Definition higher_identity
  := two_sphere_cylinder_map_id X b KRX KCX.

(** Retain the complete composition interface, including independent
    intermediate choices, without re-expanding its dependent endpoints. *)

(** 保留含独立中间选择的完整复合接口，不重新展开其依赖端点。 *)

Definition higher_composition
  := two_sphere_cylinder_map_comp KRX KCX KRY KCY KRZ KCZ α β b.

(** Product preservation needs only target missing-face-two comparison,
    with no source four-dimensional choice or group. *)

(** 乘法保持只需目标缺第二面比较，无须来源四维选择或群。 *)

Definition higher_minimal_product
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺) (x y : CX)
  := two_sphere_cylinder_map_mul α b KRX KCX KRY KCY H K x y.

(** A source left choice suffices to map inverses into a target group. *)

(** 来源左选择已足以将逆映到目标群。 *)

Definition higher_minimal_inverse
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}
    `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺) (x : CX)
  := two_sphere_cylinder_map_left_inverse α b KRX KCX KRY KCY I H K L x.

(** Importing map laws does not select algebraic models or raw equivalence. *)

(** 导入映射定律不选择代数模型或原始等价。 *)

Fail Definition higher_no_group_source : HasMagma CX
  := ltac:(typeclasses eauto).
Fail Definition higher_no_group_target : HasMagma CY
  := ltac:(typeclasses eauto).
Fail Definition higher_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition higher_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Y (α 0 b))
  := ltac:(typeclasses eauto).

End Higher.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_map_resp.
