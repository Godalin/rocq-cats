From Cats Require Export
  Cat.Computational.Arrow.Premonoidal
  Cat.Monoidal.CartesianSymmetric.

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
    (A : Arrow C K (@CartHasMonoidal C HT HP)).

(** Use pure exchange with the same premonoidal choices.
    Coherence is inherited under the pure functor from cartesian values. *)

(** 在同一份预幺半选择上使用纯交换。相干性沿纯函子继承自笛卡尔值。 *)

Program Definition ArrowHasTensorSym
  : @HasTensorSym (ComputationCat A) (ArrowHasBinoidal A)
  :=
  {|tensor_sym X Y := arr[A; ⟨π2, π1⟩]
  ; tensor_sym_central X Y := arrow_pure_central A _
  ; tensor_sym_involutive X Y := arrow_exchange_inv A X Y
  |}.
Next Obligation.
  change (arr[A; (⟨π2, π1⟩ : Hom (X' × Y) (Y × X'))] ∘
    first[A; f; Y] ≈ second[A; f; Y] ∘
      arr[A; (⟨π2, π1⟩ : Hom (X × Y) (Y × X))]).
  unfold arrow_first.
  rewrite <- !comp_assoc, arrow_exchange_inv, comp_id_l. reflexivity.
Defined.
(** The pure functor carries the cartesian hexagon to computations. *)

(** 纯函子将笛卡尔六边形送到计算范畴。 *)

Program Definition ArrowIsSymHexagon
  : @IsSymHexagon (ComputationCat A) (ArrowHasBinoidal A)
      ArrowHasTensorSym (ArrowHasAssociator A)
  :=
  {|tensor_sym_hexagon := _|}.
Next Obligation.
  change (arr[A; (@product_assoc C HP Y Z X).1] ∘
    (arr[A; ⟨π2, π1⟩] ∘ arr[A; (@product_assoc C HP X Y Z).1]) ≈
    second[A; arr[A; (⟨π2, π1⟩ : Hom (X × Z) (Z × X))]; Y] ∘
      (arr[A; (@product_assoc C HP Y X Z).1] ∘
        first[A; arr[A; (⟨π2, π1⟩ : Hom (X × Y) (Y × X))]; Z])).
  rewrite arrow_second_arr, arrow_first_arr, <- !fmap_comp.
  apply fmap_proper.
  exact (tensor_sym_hexagon
    (H := @CartIsSymHexagon C HT HP) X Y Z).
Defined.
(** The pure functor also preserves the exchange equation for unitors. *)

(** 纯函子也保持交换与单位子的相容方程。 *)

Program Definition ArrowIsSymUnit
  : @IsSymUnit (ComputationCat A) (ArrowHasBinoidal A)
      ArrowHasTensorSym (ArrowHasUnitors A)
  :=
  {|tensor_sym_unit := _|}.
Next Obligation.
  change (arr[A; (π2 : Hom (1 × X) X)] ∘ arr[A; ⟨π2, π1⟩] ≈
    arr[A; (π1 : Hom (X × 1) X)]).
  rewrite <- fmap_comp. apply fmap_proper.
  exact (tensor_sym_unit
    (H := @CartIsSymUnit C HT HP) X).
Defined.

(** Add pure exchange to the existing premonoidal computation category. *)

(** 为已有预幺半计算范畴加入纯交换。 *)

Definition ArrowSymPremonoidal
  : SymPremonoidalCat
  := SymPremonoidalCatOfPremonoidalCat
       (ArrowPremonoidal A) ArrowHasTensorSym ArrowIsSymHexagon ArrowIsSymUnit.

End Cartesian.
