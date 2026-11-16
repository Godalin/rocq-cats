From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderBase.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_change_base_resp.

(** * Independent Native and Common Lift Bounds

    Retain both strict native orders, both strict final lift orders and
    the weakest complete interfaces, without enabling any algebra model. *)

(** * 独立原生界及共同提升界

    保留两种严格原生次序、两种严格最终提升次序及最弱完整接口，不启用代数模型。 *)

(** ** Lower Equality Bound

    Fix one simplicial object, three vertices and three independent
    presentations. The two supplied vertex equalities retain their witnesses. *)

(** ** 较低相等界

    固定一个单纯对象、三个顶点及三份独立呈现；两份给定顶点相等保留其见证。 *)

Section Lower.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).
Context (b c d : X 0) (E : b ≈S c) (F : c ≈S d).
Context (KR KR' KR'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC KC' KC'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The map needs only presentation choices and specified equality. *)

(** 映射只需要呈现选择及指定相等。 *)

Definition lower_map
  : TwoSphereCylinderS X b KR KC →r TwoSphereCylinderS X c KR' KC'
  := two_sphere_cylinder_change_base_resp X KR KC KR' KC' E.

(** Retain each full coherence interface at these strict native bounds. *)

(** 在这些严格原生界处保留各项完整相干接口。 *)

Definition lower_identity
  := two_sphere_cylinder_change_base_id X KR KC b.

Definition lower_witness
  := two_sphere_cylinder_change_base_witness X KR KC KR' KC' E E.

Definition lower_composition
  := two_sphere_cylinder_change_base_comp X KR KC KR' KC' KR'' KC'' E F.

Definition lower_unit
  := two_sphere_cylinder_change_base_unit X KR KC KR' KC' E.

(** Product comparison adds only four-dimensional missing-face-two choice. *)

(** 乘积比较只增加四维缺第二面选择。 *)

Definition lower_minimal_product
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS X b)
  := two_sphere_cylinder_change_base_mul X KR KC KR' KC' E H K x y.

(** Only the source left choice and the target group choices are supplied. *)

(** 仅提供来源左选择及目标群选择。 *)

Definition lower_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS X b)
  := two_sphere_cylinder_change_base_left_inverse X KR KC KR' KC'
      E I H K L x.

(** Common upward lifts retain either independent final size order. *)

(** 共同向上提升保留两种独立最终大小次序。 *)

Definition lower_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

Definition lower_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

(** Neither algebra nor full Kan nor raw cylinder equivalence is selected. *)

(** 不选择代数、完整 Kan 或原始柱等价。 *)

Fail Definition lower_no_group : HasMagma (TwoSphereCylinderS X b KR KC)
  := ltac:(typeclasses eauto).
Fail Definition lower_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition lower_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X c)
  := ltac:(typeclasses eauto).

End Lower.

(** ** Higher Equality Bound

    Fix one simplicial object, three vertices and three independent
    presentations. The two supplied vertex equalities retain their witnesses. *)

(** ** 较高相等界

    固定一个单纯对象、三个顶点及三份独立呈现；两份给定顶点相等保留其见证。 *)

Section Higher.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (b c d : X 0) (E : b ≈S c) (F : c ≈S d).
Context (KR KR' KR'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC KC' KC'' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The map needs only presentation choices and specified equality. *)

(** 映射只需要呈现选择及指定相等。 *)

Definition higher_map
  : TwoSphereCylinderS X b KR KC →r TwoSphereCylinderS X c KR' KC'
  := two_sphere_cylinder_change_base_resp X KR KC KR' KC' E.

(** Retain each full coherence interface at these strict native bounds. *)

(** 在这些严格原生界处保留各项完整相干接口。 *)

Definition higher_identity
  := two_sphere_cylinder_change_base_id X KR KC b.

Definition higher_witness
  := two_sphere_cylinder_change_base_witness X KR KC KR' KC' E E.

Definition higher_composition
  := two_sphere_cylinder_change_base_comp X KR KC KR' KC' KR'' KC'' E F.

Definition higher_unit
  := two_sphere_cylinder_change_base_unit X KR KC KR' KC' E.

(** Product comparison adds only four-dimensional missing-face-two choice. *)

(** 乘积比较只增加四维缺第二面选择。 *)

Definition higher_minimal_product
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS X b)
  := two_sphere_cylinder_change_base_mul X KR KC KR' KC' E H K x y.

(** Only the source left choice and the target group choices are supplied. *)

(** 仅提供来源左选择及目标群选择。 *)

Definition higher_minimal_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS X b)
  := two_sphere_cylinder_change_base_left_inverse X KR KC KR' KC'
      E I H K L x.

(** Common upward lifts retain either independent final size order. *)

(** 共同向上提升保留两种独立最终大小次序。 *)

Definition higher_higher_final_iso
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

Definition higher_lower_final_iso
  : LiftS@{_ _ q v} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereCylinderS X c KR' KC')
  := two_sphere_cylinder_change_base_iso X KR KC KR' KC' E.

(** Neither algebra nor full Kan nor raw cylinder equivalence is selected. *)

(** 不选择代数、完整 Kan 或原始柱等价。 *)

Fail Definition higher_no_group : HasMagma (TwoSphereCylinderS X b KR KC)
  := ltac:(typeclasses eauto).
Fail Definition higher_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition higher_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X c)
  := ltac:(typeclasses eauto).

End Higher.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence
  two_sphere_cylinder_class_iff two_sphere_cylinder_change_base_resp.
