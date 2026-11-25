From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereFaceHomotopy.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Face Conversion with Independent Sizes and Minimal Choices

    The supplied-filler interface has no selection assumption. The chosen
    interface asks only for missing face one in dimension four. Check both
    with simplex equality strictly below and strictly above its carrier. *)

(** * 独立大小与最小选择下的面转换

    给定填充接口没有选择假设；选定接口只要求四维缺第一面。在单形相等严格
    低于及严格高于载体两种情况下检查。 *)

(** ** Strict Profiles

    Fix three strictly increasing bounds, without any global Kan choice. *)

(** ** 严格配置

    固定三个严格递增界，不提供任何全局 Kan 选择。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** The actual horn retains the independent value/equality profile. *)

(** 实际 horn 保留独立的值／相等配置。 *)

Definition lower_horn
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : HornS X 4 fin_first⁺
  := SphereLowHomotopyHornN X b H.

(** A supplied actual filler needs no chosen filling structure. *)

(** 给定实际填充无需选定填充结构。 *)

Definition lower_supplied
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
    (V : X 4) (HV : is_horn_filler (SphereLowHomotopyHornN X b H) V)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopyOfFiller X b H V HV.

(** Only the single four-dimensional horn choice is assumed. *)

(** 只假设这一项四维 horn 选择。 *)

Definition lower_chosen
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopy X b H.

(** Descent uses the same actual conversion and generated relation. *)

(** 下降使用同一实际转换及生成关系。 *)

Definition lower_class
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_low_homotopy_class X b H.

(** Endpoint respectfulness does not require any selected filler. *)

(** 端点保相等不要求任何选定填充。 *)

Definition lower_endpoints
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x x' y y' : TwoSphereS X b) (E : x ≈S x') (F : y ≈S y')
  : TwoSphereLowHomotopy X b x y ↔ TwoSphereLowHomotopy X b x' y'
  := TwoSphereLowHomotopy_proper X b x x' E y y' F.

(** The actual horn retains the independent value/equality profile. *)

(** 实际 horn 保留独立的值／相等配置。 *)

Definition higher_horn
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : HornS X 4 fin_first⁺
  := SphereLowHomotopyHornN X b H.

(** A supplied actual filler needs no chosen filling structure. *)

(** 给定实际填充无需选定填充结构。 *)

Definition higher_supplied
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
    (V : X 4) (HV : is_horn_filler (SphereLowHomotopyHornN X b H) V)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopyOfFiller X b H V HV.

(** Only the single four-dimensional horn choice is assumed. *)

(** 只假设这一项四维 horn 选择。 *)

Definition higher_chosen
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : TwoSphereHomotopy X b x y
  := SphereLowHomotopy X b H.

(** Descent uses the same actual conversion and generated relation. *)

(** 下降使用同一实际转换及生成关系。 *)

Definition higher_class
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    (x y : TwoSphereS X b) (H : TwoSphereLowHomotopy X b x y)
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_low_homotopy_class X b H.

(** Endpoint respectfulness does not require any selected filler. *)

(** 端点保相等不要求任何选定填充。 *)

Definition higher_endpoints
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x x' y y' : TwoSphereS X b) (E : x ≈S x') (F : y ≈S y')
  : TwoSphereLowHomotopy X b x y ↔ TwoSphereLowHomotopy X b x' y'
  := TwoSphereLowHomotopy_proper X b x x' E y y' F.

End StrictSizes.
