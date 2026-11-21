From Cats Require Export
  Cat.Computational.Arrow.Binoidal
  Cat.Monoidal.PremonoidalLaws.

Local Open Scope computation_scope.

(** * Premonoidal Computations from Cartesian Arrows

    Keep the existing two context actions and lift the value category's
    selected structural isomorphisms through its pure-arrow functor.
    Separate naturality follows from the Arrow laws; coherence is the
    pure image of value coherence. This construction requires the named
    terminal and product choices, not exponentials or effect interchange. *)

(** * 从笛卡尔 Arrow 得到预幺半计算

    保留已有两种上下文作用，沿纯态射函子提升值范畴的选定结构同构。
    分别自然性来自 Arrow 定律，相干性是值相干性的纯像。本构造要求具名的
    终对象与积选择，不要求指数对象或效应交换律。 *)

Section Cartesian.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartHasMonoidal C HT HP)).

Let V
  : HasMonoidal C
  := CartHasMonoidal.

Let J
  : Fct C (ComputationCat A)
  := ArrowPureF A.

(** All structural inverses are the pure images of the same selected
    value inverses. The generic functor theorem supplies their inverse
    equations. The binoidal parent is exactly [ArrowBinoidal A], so no
    context operations or tensor choices are duplicated. Importing this
    module does not select a default computation structure. *)

(** 全部结构逆都是同一选定值逆的纯像，其互逆方程来自一般函子定理。
    双侧张量父结构恰好为 [ArrowBinoidal A]，故不重复上下文运算或张量选择。
    导入本模块不会选定默认计算结构。 *)

Program Definition ArrowHasAssociator
  : @HasTensorAssoc (ComputationCat A) (ArrowHasBinoidal A)
  :=
  {|TensorAssocRIso X Y :=
      ({|nt Z := fmap J (@tensor_assoc C _ V X Y Z).1
        ; nat_naturality Z Z' h := arrow_context_assoc A h
        |}; λ Z,
          let i := @tensor_assoc C _ V X Y Z in
          fct_is_iso J i.1 i.2)
  ; isTensorAssoc :=
      {|assoc_natural_l Y Z :=
          {|nat_iso_naturality X X' f := arrow_first_assoc A f|}
      ; assoc_natural_m X Z :=
          {|nat_iso_naturality Y Y' g := arrow_middle_assoc A g|}
      ; assoc_central X Y Z := arrow_pure_central A _
      |}
  |}.
Next Obligation.
  change (arr[A; (@product_assoc C HP W X (Y × Z)).1] ∘
    arr[A; (@product_assoc C HP (W × X) Y Z).1] ≈
    second[A; arr[A; (@product_assoc C HP X Y Z).1]; W] ∘
      (arr[A; (@product_assoc C HP W (X × Y) Z).1] ∘
        first[A; arr[A; (@product_assoc C HP W X Y).1]; Z])).
  rewrite arrow_second_arr, arrow_first_arr, <- !fmap_comp.
  apply fmap_proper.
  exact (@tensor_assoc_pentagon C _ V W X Y Z).
Defined.

(** Lift only the unitors, with no dependence on the computation
    associator. Their naturality follows from the projection laws. *)

(** 只提升单位子，不依赖计算结合子；其自然性来自投影定律。 *)

Program Definition ArrowHasUnitors
  : @HasTensorUnitors (ComputationCat A) (ArrowHasBinoidal A)
  :=
  {|tensor_unit := tensor_unit V
  ; TensorUnitorLIso :=
      ({|nt X := fmap J (@tensor_unitor_l C _ V X).1
        ; nat_naturality X Y f := arrow_second_projection A f 1
        |}; λ X,
          let i := @tensor_unitor_l C _ V X in
          fct_is_iso J i.1 i.2)
  ; TensorUnitorRIso :=
      ({|nt X := fmap J (@tensor_unitor_r C _ V X).1
        ; nat_naturality X Y f := arrow_first_projection A f 1
        |}; λ X,
          let i := @tensor_unitor_r C _ V X in
          fct_is_iso J i.1 i.2)
  ; isTensorUnitors :=
      {|unitor_l_central X := arrow_pure_central A _
      ; unitor_r_central X := arrow_pure_central A _
      |}
  |}.

(** Their compatibility is the pure image of the value triangle. *)

(** 二者的相容性是值三角形的纯像。 *)

Program Definition ArrowIsPremonoidal
  : @IsPremonoidal (ComputationCat A) (ArrowHasBinoidal A)
      ArrowHasAssociator ArrowHasUnitors
  :=
  {|tensor_triangle := _|}.
Next Obligation.
  change (second[A; arr[A; (π2 : Hom (1 × Y) Y)]; X] ∘
    arr[A; (@product_assoc C HP X 1 Y).1] ≈
    first[A; arr[A; (π1 : Hom (X × 1) X)]; Y]).
  rewrite arrow_second_arr, arrow_first_arr, <- fmap_comp.
  apply fmap_proper.
  exact (tensor_triangle (IP := HasMonoidal_isPremonoidal V) X Y).
Defined.

(** Pack the same tensor, associator and coherent unitors. *)

(** 打包同一份张量、结合子与相干单位子。 *)

Definition ArrowPremonoidal
  : PremonoidalCat
  := PremonoidalCatOfBinoidalCat (ArrowBinoidal A)
       ArrowHasAssociator ArrowHasUnitors ArrowIsPremonoidal.

End Cartesian.
