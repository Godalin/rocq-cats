From Cats Require Export
  Cat.Computational.Arrow.Binoidal
  Cat.Premonoidal.Laws.

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
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

Let V
  : MonoidalCat C
  := CartesianMonoidal.

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

Program Definition ArrowPremonoidal
  : PremonoidalCat (ComputationCat A)
  :=
  {|PremonoidalB := ArrowBinoidal A
  ; PremonoidalUnit := PremonoidalUnit V
  ; premonoidal_associator X Y Z :=
      let i := @premonoidal_associator C V X Y Z in
      (fmap J i.1; functor_is_iso J i.1 i.2)
  ; premonoidal_left_unitor X :=
      let i := @premonoidal_left_unitor C V X in
      (fmap J i.1; functor_is_iso J i.1 i.2)
  ; premonoidal_right_unitor X :=
      let i := @premonoidal_right_unitor C V X in
      (fmap J i.1; functor_is_iso J i.1 i.2)
  ; premonoidal_assoc_central X Y Z := arrow_pure_central A _
  ; premonoidal_unit_l_central X := arrow_pure_central A _
  ; premonoidal_unit_r_central X := arrow_pure_central A _
  ; premonoidal_unit_l_natural X Y f := arrow_second_projection A f 1
  ; premonoidal_unit_r_natural X Y f := arrow_first_projection A f 1
  ; premonoidal_assoc_natural_l X X' Y Z f := arrow_first_assoc A f
  ; premonoidal_assoc_natural_m Y Y' X Z g := arrow_middle_assoc A g
  ; premonoidal_assoc_natural_r Z Z' X Y h := arrow_context_assoc A h
  |}.
Next Obligation.
  change (arr[A; (@product_assoc C HP W X (Y × Z)).1] ∘
    arr[A; (@product_assoc C HP (W × X) Y Z).1] ≈
    second[A; arr[A; (@product_assoc C HP X Y Z).1]; W] ∘
      (arr[A; (@product_assoc C HP W (X × Y) Z).1] ∘
        first[A; arr[A; (@product_assoc C HP W X Y).1]; Z])).
  rewrite arrow_second_arr, arrow_first_arr, <- !functor_comp.
  apply functor_fmap_proper.
  exact (@premonoidal_pentagon C V W X Y Z).
Defined.
Next Obligation.
  change (second[A; arr[A; (π2 : Hom (1 × Y) Y)]; X] ∘
    arr[A; (@product_assoc C HP X 1 Y).1] ≈
    first[A; arr[A; (π1 : Hom (X × 1) X)]; Y]).
  rewrite arrow_second_arr, arrow_first_arr, <- functor_comp.
  apply functor_fmap_proper.
  exact (@premonoidal_triangle C V X Y).
Defined.

End Cartesian.
