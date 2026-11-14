From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMap.

Local Open Scope nat_scope.

(** * Independent Sizes for Generic Sphere-Class Maps

    Generated class witnesses may exceed simplex equality. All lifted
    comparisons use genuine upward bounds, in either strict order for
    their final carrier and equality sizes. *)

(** * 通用球面类映射的独立大小

    生成类见证可以超过单形相等。全部提升比较使用真正的向上界，最终载体与
    相等大小可有任一种严格次序。 *)

Section IndependentSizes.
Universes l u p v q.
Constraint l < u, u < p, p < v, v < q.

(** Natural isomorphism at lower ambient and higher final equality. *)

(** 此环境及最终相等配置下的自然同构。 *)

Definition lower_ambient_higher_common_iso
    (X Y : Functor (Δ^op) SetCat@{u l _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Natural isomorphism at lower ambient and lower final equality. *)

(** 此环境及最终相等配置下的自然同构。 *)

Definition lower_ambient_lower_common_iso
    (X Y : Functor (Δ^op) SetCat@{u l _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ q v} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ q v} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Equality transport at lower ambient equality. *)

(** 此环境相等配置下的相等运输。 *)

Definition lower_ambient_base_iso
    (X : Functor (Δ^op) SetCat@{u l _ _ _ _ _})
    (b c : X 0) (E : b ≈S c)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS X c)
  := two_sphere_class_change_base_iso X E.

(** Actual composition witnesses at lower ambient equality. *)

(** 此环境相等配置下的实际合成见证。 *)

Definition lower_ambient_composite_map
    (X Y : Functor (Δ^op) SetCat@{u l _ _ _ _ _})
    (α : X ⇒ Y) (b : X 0) (x y z : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite Y (α 0 b)
      (two_sphere_map_resp α b x) (two_sphere_map_resp α b y)
      (two_sphere_map_resp α b z)
  := two_sphere_composite_map α b H.

(** Natural isomorphism at higher ambient and higher final equality. *)

(** 此环境及最终相等配置下的自然同构。 *)

Definition higher_ambient_higher_common_iso
    (X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Natural isomorphism at higher ambient and lower final equality. *)

(** 此环境及最终相等配置下的自然同构。 *)

Definition higher_ambient_lower_common_iso
    (X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0)
  : LiftS@{_ _ q v} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ q v} (TwoSphereClassS Y (α 0 b))
  := two_sphere_class_iso α Hα b.

(** Equality transport at higher ambient equality. *)

(** 此环境相等配置下的相等运输。 *)

Definition higher_ambient_base_iso
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
    (b c : X 0) (E : b ≈S c)
  : LiftS@{_ _ v q} (TwoSphereClassS X b) ≅[SetCat]
      LiftS@{_ _ v q} (TwoSphereClassS X c)
  := two_sphere_class_change_base_iso X E.

(** Actual composition witnesses at higher ambient equality. *)

(** 此环境相等配置下的实际合成见证。 *)

Definition higher_ambient_composite_map
    (X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
    (α : X ⇒ Y) (b : X 0) (x y z : TwoSphereS X b)
    (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite Y (α 0 b)
      (two_sphere_map_resp α b x) (two_sphere_map_resp α b y)
      (two_sphere_map_resp α b z)
  := two_sphere_composite_map α b H.

End IndependentSizes.
