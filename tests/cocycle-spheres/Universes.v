From Cats Require Import
  Instance.Bool.CocycleSphere.
From Cats Require
  Instance.Set.Simplicial.Vertex.Core.

Import Cats.Instance.Set.Groupoid (EqGpd).
Import Cats.Instance.Set.Simplicial.Vertex.Core (VertexNerve).

(** * Sphere Classes at Strictly Different Sizes

    The retained boundary and homotopy witnesses may enlarge the class
    setoid. Its original ambient simplex sizes remain independent, as do
    the coefficient carrier/equality sizes and the final common lifts. *)

(** * 严格不同大小中的球面类

    保留的边界与同伦见证可以扩大类广集；原环境单形大小仍独立，系数载体／
    相等大小及最终共同提升大小也仍独立。 *)

Section CoefficientSizes.
Universes e h l u p v q.
Constraint e < h, h < l, l < u, u < p, p < v, v < q.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Monoid M} `{HN : !Monoid N}.

(** Lower native equality and lower ambient equality. *)

(** 较低原生相等及较低环境相等。 *)

Definition lower_native_lower_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} M
  := cocycle_two_sphere_class_iso.

(** Lower native equality and higher ambient equality. *)

(** 较低原生相等及较高环境相等。 *)

Definition lower_native_higher_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} M
  := cocycle_two_sphere_class_iso.

(** Higher native equality and lower ambient equality. *)

(** 较高原生相等及较低环境相等。 *)

Definition higher_native_lower_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} N
  := cocycle_two_sphere_class_iso.

(** Higher native equality and higher ambient equality. *)

(** 较高原生相等及较高环境相等。 *)

Definition higher_native_higher_ambient_class_iso
  : LiftS@{_ _ v q}
      (TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ v q} N
  := cocycle_two_sphere_class_iso.

(** The final common equality bound may lie below its carrier bound. *)

(** 最终共同相等界可以低于其载体界。 *)

Definition lower_common_equality_class_iso
  : LiftS@{_ _ q v}
      (TwoSphereClassS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ q v} M
  := cocycle_two_sphere_class_iso.

(** The opposite native profile retains the same independent common lifts. *)

(** 相反原生配置也保留同样独立的共同提升。 *)

Definition reverse_lower_common_equality_class_iso
  : LiftS@{_ _ q v}
      (TwoSphereClassS (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0)) ≅[SetCat] LiftS@{_ _ q v} N
  := cocycle_two_sphere_class_iso.

End CoefficientSizes.

(** ** Ordinary Categories with Independent Native Hom Sizes

    The obstruction does not force hom equality to the hom carrier size,
    and works at both strict ambient equality orders. *)

(** ** 原生 Hom 大小独立的普通范畴

    障碍不迫使 Hom 相等与 Hom 载体大小相同，两种严格环境相等次序均可使用。 *)

Section NerveSizes.
Local Existing Instance BoolS_Monoid.
Universes e h o l u p.
Constraint e < h, h < o, o < l, l < u, u < p.
Context (A : SetC@{o e}) (C : Cat@{o h e l l})
    (T : Fct (EqGpd A) C).

(** Lower ambient equality retains the obstruction. *)

(** 较低环境相等保留该障碍。 *)

Definition lower_equality_nerve_obstruction
  : ¬ ((Z²(BoolS) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ≅N
      (VertexNerve T : Fct (Δ^op) SetCat@{u o _ _ _ _ _}))
  := bool_cocycle_not_vertex_nerve T.

(** Higher ambient equality retains the same obstruction. *)

(** 较高环境相等也保留同样的障碍。 *)

Definition higher_equality_nerve_obstruction
  : ¬ ((Z²(BoolS) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      (VertexNerve T : Fct (Δ^op) SetCat@{u p _ _ _ _ _}))
  := bool_cocycle_not_vertex_nerve T.

End NerveSizes.
