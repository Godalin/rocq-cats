From Cats Require Import
  Instance.Set.Simplicial.Cocycle.SphereGroup.

(** * Group Constructions at Strictly Different Sizes

    The coefficient carrier and equality sizes remain independent, as do
    the ambient simplex sizes. The generated class witnesses may live at
    larger bounds; no resizing axiom or equality of bounds is required. *)

(** * 严格不同大小下的群构造

    系数载体与相等大小保持独立，环境单形大小也保持独立。生成类见证可以处于
    更高的界；不要求重设大小公理或大小界的相等。 *)

Section GroupSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Group M} `{HN : !Group N}.

(** Lower native and lower ambient equality. *)

(** 较低原生相等与较低环境相等。 *)

Definition lower_native_lower_ambient_group
  : Group (TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  := cocycle_two_sphere_Group.

(** Lower native and higher ambient equality. *)

(** 较低原生相等与较高环境相等。 *)

Definition lower_native_higher_ambient_group
  : Group (TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  := cocycle_two_sphere_Group.

(** Higher native and lower ambient equality. *)

(** 较高原生相等与较低环境相等。 *)

Definition higher_native_lower_ambient_group
  : Group (TwoSphereClassS
      (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  := cocycle_two_sphere_Group.

(** Higher native and higher ambient equality. *)

(** 较高原生相等与较高环境相等。 *)

Definition higher_native_higher_ambient_group
  : Group (TwoSphereClassS
      (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  := cocycle_two_sphere_Group.

Context `{HC : !IsCommutativeMonoid M} `{HD : !IsCommutativeMonoid N}.

(** Commutativity keeps the same parent at lower ambient equality. *)

(** 较低环境相等中的交换性保持同一父结构。 *)

Definition lower_ambient_commutativity
  : @IsCommutativeMonoid
      (TwoSphereClassS
        (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
        (two_cocycle_simplex_unit 0))
      (GroupM lower_native_lower_ambient_group)
  := cocycle_two_sphere_IsCommutativeMonoid.

(** The opposite native profile accepts higher ambient equality too. *)

(** 相反原生配置也接受较高环境相等。 *)

Definition higher_ambient_commutativity
  : @IsCommutativeMonoid
      (TwoSphereClassS
        (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (two_cocycle_simplex_unit 0))
      (GroupM higher_native_higher_ambient_group)
  := cocycle_two_sphere_IsCommutativeMonoid.

End GroupSizes.

(** ** Geometric Witnesses at Independent Sizes

    The actual tetrahedron and its sphere-class comparison must also
    accept the two opposite strict ambient equality profiles. *)

(** ** 独立大小中的几何见证

    实际四面体及其球面类比较，也须接受两种相反的严格环境相等配置。 *)

Section FillerSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : SetC@{h e}) `{HM : !Monoid M}.

(** Lower ambient equality with retained simplex data. *)

(** 较低环境相等，保留单形数据。 *)

Definition lower_ambient_composite
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereComposite _ _ x y (cocycle_two_sphere_mul x y)
  := CocycleTwoSphereMul x y.

(** Higher ambient equality with the same construction. *)

(** 较高环境相等，使用同一构造。 *)

Definition higher_ambient_composite
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereComposite _ _ x y (cocycle_two_sphere_mul x y)
  := CocycleTwoSphereMul x y.

End FillerSizes.
