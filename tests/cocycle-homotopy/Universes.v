From Cats Require Import
  Instance.Bool.CocycleHomotopy.

Import Cats.Instance.Set.Groupoid (EqGpd).
Import Cats.Instance.Set.Simplicial.Vertex.Core (VertexNerve).

Local Open Scope nat_scope.

(** * Map Invariants at Independent Sizes

    Probe opposite strict coefficient profiles and both ambient equality
    orders. The generated map witnesses are not forced into either native
    coefficient equality or the original simplex equality bound. *)

(** * 独立大小中的映射不变量

    检查相反的严格系数配置及两种环境相等次序。生成映射见证不被迫进入原生
    系数相等界或原有单形相等界。 *)

Section CoefficientSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Monoid M} `{HN : !Monoid N}.

(** The lower native / lower ambient evaluation
    retains the whole generated map relation. *)

(** 此原生与环境大小配置的求值保留完整生成映射关系。 *)

Definition lower_native_lower_ambient_evaluation
    (X : Functor (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS M _ X →r M
  := cocycle_homotopy_evaluation_resp b x.

(** The lower native / higher ambient evaluation
    retains the whole generated map relation. *)

(** 此原生与环境大小配置的求值保留完整生成映射关系。 *)

Definition lower_native_higher_ambient_evaluation
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS M _ X →r M
  := cocycle_homotopy_evaluation_resp b x.

(** The higher native / lower ambient evaluation
    retains the whole generated map relation. *)

(** 此原生与环境大小配置的求值保留完整生成映射关系。 *)

Definition higher_native_lower_ambient_evaluation
    (X : Functor (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS N _ X →r N
  := cocycle_homotopy_evaluation_resp b x.

(** The higher native / higher ambient evaluation
    retains the whole generated map relation. *)

(** 此原生与环境大小配置的求值保留完整生成映射关系。 *)

Definition higher_native_higher_ambient_evaluation
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x : TwoSphereS X b)
  : @CocycleHomotopyMapS N _ X →r N
  := cocycle_homotopy_evaluation_resp b x.

End CoefficientSizes.

(** ** Explicit Edge Reduction without a Model

    These probes use arbitrary targets and an explicit edge law, without
    coefficient structures or Kan choices. *)

(** ** 不依赖模型的显式边约化

    以下检查使用任意目标及显式边定律，不带系数结构或 Kan 选择。 *)

Section GenericSizes.
Universes l u p.
Constraint l < u, u < p.

(** The lower ambient equality admits the actual restricted cylinder. *)

(** 此环境相等界接受实际限制柱。 *)

Definition lower_equality_restricted_cylinder
    (X Y : Functor (Δ^op) SetCat@{u l _ _ _ _ _}) (c : Y 0)
    (E1 : ∀ z : Y 1, z ≈S simplex_constant Y c 1)
    (f g : X ⇒ Y) (H : SimplicialHomotopy f g)
    (b : X 0) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (one_reduced_sphere_resp Y c E1 (f 2 x.1))
      (one_reduced_sphere_resp Y c E1 (g 2 x.1))
  := OneReducedSphereCylinder Y c E1 H b x.

(** The higher ambient equality admits the actual restricted cylinder. *)

(** 此环境相等界接受实际限制柱。 *)

Definition higher_equality_restricted_cylinder
    (X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (c : Y 0)
    (E1 : ∀ z : Y 1, z ≈S simplex_constant Y c 1)
    (f g : X ⇒ Y) (H : SimplicialHomotopy f g)
    (b : X 0) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (one_reduced_sphere_resp Y c E1 (f 2 x.1))
      (one_reduced_sphere_resp Y c E1 (g 2 x.1))
  := OneReducedSphereCylinder Y c E1 H b x.

End GenericSizes.

(** ** A Category with Unequal Native Hom Sizes

    Ordinary category Hom equality remains smaller than its carrier;
    both ambient equality orders retain the stronger map obstruction. *)

(** ** 原生 Hom 大小不相等的范畴

    普通范畴 Hom 相等保持小于其载体；两种环境相等次序都保留更强映射障碍。 *)

Section NerveSizes.
Local Existing Instance BoolS_Monoid.
Universes e h o l u p.
Constraint e < h, h < o, o < l, l < u, u < p.
Context (A : SetC@{o e}) (C : Cat@{o h e l l})
    (T : Functor (EqGpd A) C).

(** The lower ambient equality admits the obstruction for arbitrary maps. *)

(** 此环境相等界接受任意映射的障碍。 *)

Definition lower_equality_nerve_obstruction
    (f : (Z²(BoolS) : Functor (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒
      (VertexNerve T : Functor (Δ^op) SetCat@{u o _ _ _ _ _}))
    (g : VertexNerve T ⇒ Z²(BoolS))
  : ¬ SimplicialHomotopy (g ∘Nv f) idN
  := bool_cocycle_no_nerve_forward_homotopy T f g.

(** The higher ambient equality admits the obstruction for arbitrary maps. *)

(** 此环境相等界接受任意映射的障碍。 *)

Definition higher_equality_nerve_obstruction
    (f : (Z²(BoolS) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      (VertexNerve T : Functor (Δ^op) SetCat@{u p _ _ _ _ _}))
    (g : VertexNerve T ⇒ Z²(BoolS))
  : ¬ SimplicialHomotopy (g ∘Nv f) idN
  := bool_cocycle_no_nerve_forward_homotopy T f g.

End NerveSizes.
