From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereFirstTransport.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes for First-Input Descent

    Probe lower and higher simplex equality sizes. Elementary directions
    use different minimal four-horn choices; generated transport retains
    its full witness type and needs no three-horn selection. *)

(** * 第一输入下降的独立大小

    检查较低、较高单形相等大小。初等运输的两个方向使用不同的最小四维 horn
    选择；生成运输保留完整见证类型，不要求三维 horn 选择。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Forward transport needs only missing-face-three fillers. *)

(** 正向运输只要求缺失第三面的填充。 *)

Definition lower_forward
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x x' y z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite X b x' y z
  := SphereCompositeFirstHomotopy X b G H.

(** Backward transport needs only missing-face-two fillers. *)

(** 反向运输只要求缺失第二面的填充。 *)

Definition lower_backward
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺}
    (x x' y z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x' y z)
  : TwoSphereComposite X b x y z
  := SphereCompositeFirstHomotopyBack X b G H.

(** An actual supplied filler requires no selected structure. *)

(** 给定实际填充时不要求选定结构。 *)

Definition lower_given_filler
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x x' y z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x y z)
    (V : X 4) (HV : is_horn_filler (SphereFirstForwardHornN X b G H) V)
  : TwoSphereComposite X b x' y z
  := SphereCompositeFirstOfFiller X b G H V HV.

(** Generated first-input equality retains two-way computational transport. *)

(** 第一输入的生成相等保留双向可计算运输。 *)

Definition lower_generated
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x x' y z : TwoSphereS X b) (E : (x : TwoSphereClassS X b) ≈S x')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y z
  := two_sphere_composite_first_class X b E y z.

(** The first partial operation is an actual respectful class map. *)

(** 第一输入的偏运算是实际保相等的类映射。 *)

Definition lower_partial
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (y : TwoSphereS X b)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := two_sphere_kan_composite_first_resp X b H y.

(** Forward transport needs only missing-face-three fillers. *)

(** 正向运输只要求缺失第三面的填充。 *)

Definition higher_forward
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x x' y z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite X b x' y z
  := SphereCompositeFirstHomotopy X b G H.

(** Backward transport needs only missing-face-two fillers. *)

(** 反向运输只要求缺失第二面的填充。 *)

Definition higher_backward
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 4 fin_first⁺⁺}
    (x x' y z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x' y z)
  : TwoSphereComposite X b x y z
  := SphereCompositeFirstHomotopyBack X b G H.

(** An actual supplied filler requires no selected structure. *)

(** 给定实际填充时不要求选定结构。 *)

Definition higher_given_filler
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x x' y z : TwoSphereS X b)
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x y z)
    (V : X 4) (HV : is_horn_filler (SphereFirstForwardHornN X b G H) V)
  : TwoSphereComposite X b x' y z
  := SphereCompositeFirstOfFiller X b G H V HV.

(** Generated first-input equality retains two-way computational transport. *)

(** 第一输入的生成相等保留双向可计算运输。 *)

Definition higher_generated
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x x' y z : TwoSphereS X b) (E : (x : TwoSphereClassS X b) ≈S x')
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y z
  := two_sphere_composite_first_class X b E y z.

(** The first partial operation is an actual respectful class map. *)

(** 第一输入的偏运算是实际保相等的类映射。 *)

Definition higher_partial
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (y : TwoSphereS X b)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  := two_sphere_kan_composite_first_resp X b H y.

End StrictSizes.
