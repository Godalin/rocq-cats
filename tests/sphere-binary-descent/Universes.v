From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMagma
  Instance.Set.Magma.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and Explicit Choices for Binary Descent

    Probe both equality sizes below and above the simplex carrier size.
    Supplied composites need no three-horn selection; raw multiplication
    needs only its explicit three-horn choice. Magma packaging uses the
    same minimal four-dimensional selections as the two transports. *)

(** * 二元下降的独立大小与显式选择

    分别检查低于和高于单形载体的相等大小。给定合成不需三维选择；原始乘法
    只需其显式三维选择。原群打包使用两个运输所需的同一组最小四维选择。 *)

(** ** Strictly Separated Levels

    Fix three strictly increasing levels. Each interface below is checked
    once at the lower equality level and once at the higher level. *)

(** ** 严格分离的层级

    固定三个严格递增层级。以下每个接口分别在较低及较高相等层级检查。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Two generated inputs transport supplied composites in both directions. *)

(** 两个生成输入在两个方向运输给定合成。 *)

Definition lower_transport
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z : TwoSphereS X b)
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y' z
  := two_sphere_composite_class X b E F z.

(** Supplied composites can be compared without a dimension-three choice. *)

(** 无须三维选择即可比较给定合成。 *)

Definition lower_comparison
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x' y' z')
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : (z : TwoSphereClassS X b) ≈S z'
  := two_sphere_composite_output_class_eq X b H K E F.

(** Raw multiplication requires only its explicit three-horn choice. *)

(** 原始乘法只要求其显式三维 horn 选择。 *)

Definition lower_raw_mul
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : TwoSphereClassS X b → TwoSphereClassS X b → TwoSphereClassS X b
  := two_sphere_kan_mul X b H.

(** The chosen magma uses the same independently sized class setoid. *)

(** 选定原群使用同一个大小独立的类广集。 *)

Definition lower_magma
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Magma (TwoSphereClassS X b)
  := TwoSphereClassMagma X b H.

(** Independent three-horn choices give equal product-setoid maps. *)

(** 独立三维 horn 选择给出相等的积广集映射。 *)

Definition lower_choice
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
  : set_magma_mul_resp (TwoSphereClassMagma X b H) ≈f
      set_magma_mul_resp (TwoSphereClassMagma X b K)
  := two_sphere_class_magma_choice_eq X b H K.

(** Two generated inputs transport supplied composites in both directions. *)

(** 两个生成输入在两个方向运输给定合成。 *)

Definition higher_transport
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z : TwoSphereS X b)
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y' z
  := two_sphere_composite_class X b E F z.

(** Supplied composites can be compared without a dimension-three choice. *)

(** 无须三维选择即可比较给定合成。 *)

Definition higher_comparison
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (x x' y y' z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x' y' z')
    (E : (x : TwoSphereClassS X b) ≈S x')
    (F : (y : TwoSphereClassS X b) ≈S y')
  : (z : TwoSphereClassS X b) ≈S z'
  := two_sphere_composite_output_class_eq X b H K E F.

(** Raw multiplication requires only its explicit three-horn choice. *)

(** 原始乘法只要求其显式三维 horn 选择。 *)

Definition higher_raw_mul
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : TwoSphereClassS X b → TwoSphereClassS X b → TwoSphereClassS X b
  := two_sphere_kan_mul X b H.

(** The chosen magma uses the same independently sized class setoid. *)

(** 选定原群使用同一个大小独立的类广集。 *)

Definition higher_magma
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Magma (TwoSphereClassS X b)
  := TwoSphereClassMagma X b H.

(** Independent three-horn choices give equal product-setoid maps. *)

(** 独立三维 horn 选择给出相等的积广集映射。 *)

Definition higher_choice
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
  : set_magma_mul_resp (TwoSphereClassMagma X b H) ≈f
      set_magma_mul_resp (TwoSphereClassMagma X b K)
  := two_sphere_class_magma_choice_eq X b H K.

End StrictSizes.
