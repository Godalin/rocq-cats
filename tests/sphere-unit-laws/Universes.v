From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereUnit.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Minimal Choices and Independent Sizes for Unit Laws

    Separate the simplex carrier from lower and higher equality levels.
    Degenerate unit witnesses need no choices. The class laws use only
    missing-face-two output comparison, with independent explicit choices
    for multiplication and the relevant inverse candidate. *)

(** * 单位律的最小选择与独立大小

    将单形载体与较低、较高相等层级分离。退化单位见证无需选择。类定律只使用
    缺第二面的输出比较，乘法与相应逆候选的选择独立且显式给出。 *)

(** ** Strict Levels

    Fix three strictly increasing levels; each public construction/law is
    tested with simplex equality at the lower and higher level. *)

(** ** 严格层级

    固定三个严格递增层级，每个公开构造／定律均在较低和较高单形相等层级检查。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The left unit tetrahedron needs no selected filler. *)

(** 左单位四面体无需选定填充。 *)

Definition lower_left_witness
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b (two_sphere_base X b) x x
  := SphereLeftUnitComposite X b x.

(** The right unit tetrahedron needs no selected filler. *)

(** 右单位四面体无需选定填充。 *)

Definition lower_right_witness
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b x (two_sphere_base X b) x
  := SphereRightUnitComposite X b x.

(** The left unit law uses only output comparison and multiplication. *)

(** 左单位律仅使用输出比较及乘法。 *)

Definition lower_unit_l
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_base X b) x ≈S x
  := two_sphere_kan_mul_unit_l X b H x.

(** The right unit law uses only output comparison and multiplication. *)

(** 右单位律仅使用输出比较及乘法。 *)

Definition lower_unit_r
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (two_sphere_base X b) ≈S x
  := two_sphere_kan_mul_unit_r X b H x.

(** The left candidate needs only its own three-horn choice. *)

(** 左候选只需自身三维 horn 选择。 *)

Definition lower_inverse_l
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (@SphereKanLeftInverse X b K x).1 x ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_l X b H K x.

(** The right candidate needs only its own three-horn choice. *)

(** 右候选只需自身三维 horn 选择。 *)

Definition lower_inverse_r
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (@SphereKanRightInverse X b K x).1 ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_r X b H K x.

(** The left unit tetrahedron needs no selected filler. *)

(** 左单位四面体无需选定填充。 *)

Definition higher_left_witness
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b (two_sphere_base X b) x x
  := SphereLeftUnitComposite X b x.

(** The right unit tetrahedron needs no selected filler. *)

(** 右单位四面体无需选定填充。 *)

Definition higher_right_witness
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereComposite X b x (two_sphere_base X b) x
  := SphereRightUnitComposite X b x.

(** The left unit law uses only output comparison and multiplication. *)

(** 左单位律仅使用输出比较及乘法。 *)

Definition higher_unit_l
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_base X b) x ≈S x
  := two_sphere_kan_mul_unit_l X b H x.

(** The right unit law uses only output comparison and multiplication. *)

(** 右单位律仅使用输出比较及乘法。 *)

Definition higher_unit_r
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (two_sphere_base X b) ≈S x
  := two_sphere_kan_mul_unit_r X b H x.

(** The left candidate needs only its own three-horn choice. *)

(** 左候选只需自身三维 horn 选择。 *)

Definition higher_inverse_l
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (@SphereKanLeftInverse X b K x).1 x ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_l X b H K x.

(** The right candidate needs only its own three-horn choice. *)

(** 右候选只需自身三维 horn 选择。 *)

Definition higher_inverse_r
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺) (x : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H x (@SphereKanRightInverse X b K x).1 ≈S
      (two_sphere_base X b : TwoSphereClassS X b)
  := two_sphere_kan_mul_inverse_r X b H K x.

End StrictSizes.
