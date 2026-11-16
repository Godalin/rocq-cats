From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereHomotopyEquivalence
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and One-Sided Comparison Choices *)

(** * 独立大小与单侧比较选择 *)

(** ** Strict Profiles

    Compare both strict carrier/equality orders and independent common
    upward lifts. The left law has no target choices; the right law has
    no source choices. Neither law requires three-dimensional fillers. *)

(** ** 严格配置

    检查两种严格载体／相等次序及独立共同向上提升。左律没有目标选择，右律
    没有来源选择，二者都无需三维填充。 *)

Section StrictSizes.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.

(** The corrected reverse map requires no filling choices. *)

(** 校正反向映射无需填充选择。 *)

Definition lower_inverse
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
  : TwoSphereClassS Y (f 0 b) →r TwoSphereClassS X b
  := two_sphere_class_homotopy_inverse_resp f g b H E.

(** No target horn choices occur in the left law. *)

(** 左律没有目标 horn 选择。 *)

Definition lower_left
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (x : TwoSphereClassS X b)
  : two_sphere_class_homotopy_inverse_resp f g b H E
      (two_sphere_class_map_resp f b x) ≈S x
  := two_sphere_class_homotopy_inverse_l f g b H E x.

(** Reflection consumes arbitrary generated equality, not native equality. *)

(** 反映性消费任意生成相等，不消费原生相等。 *)

Definition lower_reflect
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (x y : TwoSphereClassS X b)
    (F : two_sphere_class_map_resp f b x ≈S two_sphere_class_map_resp f b y)
  : x ≈S y
  := two_sphere_class_map_homotopy_reflect f g b H E x y F.

(** The right law uses only Y's comparisons, independently of X's. *)

(** 右律仅用 Y 的比较，与 X 的选择独立。 *)

Definition lower_right
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    (K : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (y : TwoSphereClassS Y (f 0 b))
  : two_sphere_class_map_resp f b
      (two_sphere_class_homotopy_inverse_resp f g b H E y) ≈S y
  := two_sphere_class_homotopy_inverse_r f g b H E K F y.

(** Common upward carrier/equality bounds are explicit and independent. *)

(** 共同向上载体／相等界显式且独立。 *)

Definition lower_iso_v_q
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    (K : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
  : LiftS@{_ _ v q} (TwoSphereClassS X b)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereClassS Y (f 0 b))
  := two_sphere_class_homotopy_iso f g b H E K F.

(** Common upward carrier/equality bounds are explicit and independent. *)

(** 共同向上载体／相等界显式且独立。 *)

Definition lower_iso_q_v
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    (K : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
  : LiftS@{_ _ q v} (TwoSphereClassS X b)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereClassS Y (f 0 b))
  := two_sphere_class_homotopy_iso f g b H E K F.

(** The corrected reverse map requires no filling choices. *)

(** 校正反向映射无需填充选择。 *)

Definition higher_inverse
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
  : TwoSphereClassS Y (f 0 b) →r TwoSphereClassS X b
  := two_sphere_class_homotopy_inverse_resp f g b H E.

(** No target horn choices occur in the left law. *)

(** 左律没有目标 horn 选择。 *)

Definition higher_left
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (x : TwoSphereClassS X b)
  : two_sphere_class_homotopy_inverse_resp f g b H E
      (two_sphere_class_map_resp f b x) ≈S x
  := two_sphere_class_homotopy_inverse_l f g b H E x.

(** Reflection consumes arbitrary generated equality, not native equality. *)

(** 反映性消费任意生成相等，不消费原生相等。 *)

Definition higher_reflect
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (x y : TwoSphereClassS X b)
    (F : two_sphere_class_map_resp f b x ≈S two_sphere_class_map_resp f b y)
  : x ≈S y
  := two_sphere_class_map_homotopy_reflect f g b H E x y F.

(** The right law uses only Y's comparisons, independently of X's. *)

(** 右律仅用 Y 的比较，与 X 的选择独立。 *)

Definition higher_right
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    (K : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (y : TwoSphereClassS Y (f 0 b))
  : two_sphere_class_map_resp f b
      (two_sphere_class_homotopy_inverse_resp f g b H E y) ≈S y
  := two_sphere_class_homotopy_inverse_r f g b H E K F y.

(** Common upward carrier/equality bounds are explicit and independent. *)

(** 共同向上载体／相等界显式且独立。 *)

Definition higher_iso_v_q
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    (K : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
  : LiftS@{_ _ v q} (TwoSphereClassS X b)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereClassS Y (f 0 b))
  := two_sphere_class_homotopy_iso f g b H E K F.

(** Common upward carrier/equality bounds are explicit and independent. *)

(** 共同向上载体／相等界显式且独立。 *)

Definition higher_iso_q_v
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0)
    (H : SimplicialHomotopy (g ∘Nv f) (IdN : X ⇒ X))
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant X b 1)
    (K : SimplicialHomotopy (f ∘Nv g) (IdN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
  : LiftS@{_ _ q v} (TwoSphereClassS X b)
      ≅[SetCat@{q v _ _ _ _ _}]
      LiftS@{_ _ q v} (TwoSphereClassS Y (f 0 b))
  := two_sphere_class_homotopy_iso f g b H E K F.

End StrictSizes.
