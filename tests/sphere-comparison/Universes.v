From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereKanComparison.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Minimal Comparison Choices at Independent Sizes

    Compare actual tetrahedra at lower and higher equality sizes. The
    elementary homotopy needs only a four-horn choice. The two three-horn
    choices are independent parameters, with no equality or Proper field. *)

(** * 独立大小下的最小比较选择

    在较低、较高相等大小比较实际四面体。初等同伦只要求四维 horn 选择；
    两个三维 horn 选择是独立参数，没有相等或 Proper 字段。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The actual comparison horn requires no filler choice. *)

(** 实际比较 horn 不要求填充选择。 *)

Definition lower_horn
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
  : HornS X 4 fin_first⁺⁺
  := SphereCompositeComparisonHornN X b H K.

Definition higher_horn
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
  : HornS X 4 fin_first⁺⁺
  := SphereCompositeComparisonHornN X b H K.

(** A supplied actual filler suffices, without selecting any fillers. *)

(** 给定实际填充即已足够，无需选取任何填充。 *)

Definition lower_given_filler
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
    (V : X 4) (HV : is_horn_filler (lower_horn X b x y z z' H K) V)
  : TwoSphereHomotopy X b z z'
  := SphereCompositeHomotopyOfFiller X b H K V HV.

Definition higher_given_filler
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
    (V : X 4) (HV : is_horn_filler (higher_horn X b x y z z' H K) V)
  : TwoSphereHomotopy X b z z'
  := SphereCompositeHomotopyOfFiller X b H K V HV.

(** Select only the required missing-face-two four-horn fillers. *)

(** 只选择所需的四维缺失面二填充。 *)

Definition lower_selected
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺}
    (x y z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
  : TwoSphereHomotopy X b z z'
  := SphereCompositeOutputHomotopy X b H K.

Definition higher_selected
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺}
    (x y z z' : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
  : TwoSphereHomotopy X b z z'
  := SphereCompositeOutputHomotopy X b H K.

(** Independent three-horn choices and specified-equal inputs give equal
    output classes, without assuming a three-horn class is registered. *)

(** 独立三维 horn 选择与指定相等输入给出相等输出类，无须注册三维 horn 类。 *)

Definition lower_choices
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    (x y x' y' : TwoSphereS X b) (E : x ≈S x') (F : y ≈S y')
  : ((@SphereKanComposite X b H x y).1 : TwoSphereClassS X b) ≈S
      (@SphereKanComposite X b K x' y').1
  := two_sphere_kan_composite_eq X b H K E F.

Definition higher_choices
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺}
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    (x y x' y' : TwoSphereS X b) (E : x ≈S x') (F : y ≈S y')
  : ((@SphereKanComposite X b H x y).1 : TwoSphereClassS X b) ≈S
      (@SphereKanComposite X b K x' y').1
  := two_sphere_kan_composite_eq X b H K E F.

End StrictSizes.
