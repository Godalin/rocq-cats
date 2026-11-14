From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereBasedHomotopyClass.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and a Single Trajectory Hypothesis

    Test both strict simplex carrier/equality orders. Neither endpoint
    base correction is supplied as additional data; the trajectory edge
    determines both. Only class comparison requires target horn choices. *)

(** * 独立大小与单条轨迹假设

    检查两种严格单形载体／相等次序。不额外给出两个端点基点校正；轨迹边
    确定二者。只有类比较要求目标 horn 选择。 *)

(** ** Strict Profiles

    Fix three strictly increasing bounds with no source Kan or algebra. *)

(** ** 严格配置

    固定三个严格递增界，不提供来源 Kan 或代数。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The zero-dimensional constant law uses specified equality. *)

(** 零维常值定律使用指定相等。 *)

Definition lower_constant_zero
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
  : simplex_constant X b 0 ≈S b
  := simplex_constant_zero X b.

(** No edge-uniqueness law or filling choice is assumed. *)

(** 不假设边唯一律或填充选择。 *)

Definition lower_trace
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    (n : nat) (t : (Δ[1] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) n)
  : homotopy_map H n (simplex_constant X b n, t) ≈S
      simplex_constant Y c n
  := sphere_homotopy_trace H b c E n t.

(** Both image-base equations are derived at these same bounds. *)

(** 两个像基点方程均在同样的界处导出。 *)

Definition lower_base
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    (t : bool)
  : (if t then g else f) 0 b ≈S c
  := sphere_homotopy_base H b c E t.

(** The whole relative cylinder is constructed without any Kan choice. *)

(** 构造完整相对柱无需任何 Kan 选择。 *)

Definition lower_cylinder
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (two_sphere_change_base_resp Y (sphere_homotopy_base H b c E false)
        (two_sphere_map_resp f b x))
      (two_sphere_change_base_resp Y (sphere_homotopy_base H b c E true)
        (two_sphere_map_resp g b x))
  := SphereBasedHomotopyCylinder H b c E x.

(** Only the target's two four-dimensional comparison choices are used. *)

(** 仅使用目标的两项四维比较选择。 *)

Definition lower_class_maps
    (X Y : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
  : (two_sphere_class_change_base_resp Y (sphere_homotopy_base H b c E false)
      ∘r two_sphere_class_map_resp f b) ≈f
      (two_sphere_class_change_base_resp Y (sphere_homotopy_base H b c E true)
        ∘r two_sphere_class_map_resp g b)
  := two_sphere_class_map_homotopy H b c E.

(** The zero-dimensional constant law uses specified equality. *)

(** 零维常值定律使用指定相等。 *)

Definition higher_constant_zero
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
  : simplex_constant X b 0 ≈S b
  := simplex_constant_zero X b.

(** No edge-uniqueness law or filling choice is assumed. *)

(** 不假设边唯一律或填充选择。 *)

Definition higher_trace
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    (n : nat) (t : (Δ[1] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : homotopy_map H n (simplex_constant X b n, t) ≈S
      simplex_constant Y c n
  := sphere_homotopy_trace H b c E n t.

(** Both image-base equations are derived at these same bounds. *)

(** 两个像基点方程均在同样的界处导出。 *)

Definition higher_base
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    (t : bool)
  : (if t then g else f) 0 b ≈S c
  := sphere_homotopy_base H b c E t.

(** The whole relative cylinder is constructed without any Kan choice. *)

(** 构造完整相对柱无需任何 Kan 选择。 *)

Definition higher_cylinder
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (two_sphere_change_base_resp Y (sphere_homotopy_base H b c E false)
        (two_sphere_map_resp f b x))
      (two_sphere_change_base_resp Y (sphere_homotopy_base H b c E true)
        (two_sphere_map_resp g b x))
  := SphereBasedHomotopyCylinder H b c E x.

(** Only the target's two four-dimensional comparison choices are used. *)

(** 仅使用目标的两项四维比较选择。 *)

Definition higher_class_maps
    (X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (f g : X ⇒ Y)
    (H : SimplicialHomotopy f g) (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
  : (two_sphere_class_change_base_resp Y (sphere_homotopy_base H b c E false)
      ∘r two_sphere_class_map_resp f b) ≈f
      (two_sphere_class_change_base_resp Y (sphere_homotopy_base H b c E true)
        ∘r two_sphere_class_map_resp g b)
  := two_sphere_class_map_homotopy H b c E.

End StrictSizes.
