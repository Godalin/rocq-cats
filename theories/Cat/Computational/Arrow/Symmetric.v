From Cats Require Export
  Cat.Computational.Arrow.Premonoidal
  Cat.Premonoidal.Cartesian.

Local Open Scope computation_scope.

(** * Symmetric Computational Contexts

    Pure product exchange extends the existing premonoidal Arrow model.
    Symmetry exchanges input positions, retaining sequential effects;
    it supplies no interchange law for arbitrary computations. *)

(** * 对称计算上下文

    纯积交换扩展已有预幺半 Arrow 模型。对称性交换输入位置，同时保留顺序
    效应；它不提供任意计算的交换律。 *)

Section Cartesian.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Keep exactly the same premonoidal parent and use pure exchange.
    Coherence is inherited under the pure functor from cartesian values. *)

(** 保留完全相同的预幺半父结构，并使用纯交换。相干性沿纯函子继承自笛卡尔值。 *)

Program Definition ArrowSymmetricPremonoidal
  : SymmetricPremonoidalCat (ComputationCat A)
  :=
  {|SymmetricPremonoidalP := ArrowPremonoidal A
  ; premonoidal_symmetry X Y := arr[A; ⟨π2, π1⟩]
  ; premonoidal_symmetry_central X Y := arrow_pure_central A _
  ; premonoidal_symmetry_involutive X Y := arrow_exchange_inv A X Y
  |}.
Next Obligation.
  change (arr[A; (⟨π2, π1⟩ : Hom (X' × Y) (Y × X'))] ∘
    first[A; f; Y] ≈ second[A; f; Y] ∘
      arr[A; (⟨π2, π1⟩ : Hom (X × Y) (Y × X))]).
  unfold arrow_first.
  rewrite <- !comp_assoc, arrow_exchange_inv, comp_id_l. reflexivity.
Defined.
Next Obligation.
  change (arr[A; (@product_assoc C HP Y Z X).1] ∘
    (arr[A; ⟨π2, π1⟩] ∘ arr[A; (@product_assoc C HP X Y Z).1]) ≈
    second[A; arr[A; (⟨π2, π1⟩ : Hom (X × Z) (Z × X))]; Y] ∘
      (arr[A; (@product_assoc C HP Y X Z).1] ∘
        first[A; arr[A; (⟨π2, π1⟩ : Hom (X × Y) (Y × X))]; Z])).
  rewrite arrow_second_arr, arrow_first_arr, <- !functor_comp.
  apply functor_fmap_proper.
  exact (@premonoidal_symmetry_hexagon C
    (@CartesianSymmetricPremonoidal C HT HP) X Y Z).
Defined.
Next Obligation.
  change (arr[A; (π2 : Hom (1 × X) X)] ∘ arr[A; ⟨π2, π1⟩] ≈
    arr[A; (π1 : Hom (X × 1) X)]).
  rewrite <- functor_comp. apply functor_fmap_proper.
  exact (@premonoidal_symmetry_unit C
    (@CartesianSymmetricPremonoidal C HT HP) X).
Defined.

End Cartesian.
