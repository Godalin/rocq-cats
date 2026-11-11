From Cats Require Export
  Cat.Computational.Arrow.Cartesian
  Cat.Binoidal.Center.

Local Open Scope computation_scope.

(** * Two-Sided Contexts and Central Pure Arrows

    Reindex computations by value objects and reuse the existing first
    and second operations. This supplies a binoidal category; associator
    and unitor coherence for a full premonoidal category remain a separate
    layer. No exchange of arbitrary effects is asserted. *)

(** * 双侧上下文与中心纯态射

    用值对象重索引计算，并复用已有 first 与 second 运算，得到双侧张量范畴。
    完整预幺半范畴所需的结合子与单位子相干性仍为独立层次。不主张任意效应
    之间可交换。 *)

Section Cartesian.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** The computation objects are the value objects themselves, so the
    underlying tensor needs no equality or transport of object maps. *)

(** 计算对象就是值对象本身，故底层张量无需对象映射的相等或运输。 *)

Program Definition ArrowBinoidal
  : BinoidalCat (ComputationCat A)
  :=
  {|binoidal_tensor X Y := @Prod C HP X Y
  ; binoidal_left X Y Z f := second[A; f; Z]
  ; binoidal_right X Y Z f := first[A; f; Z]
  ; binoidal_left_proper X Y Z := arrow_second_proper A Z
  ; binoidal_right_proper X Y Z := arrow_first_proper A Z
  |}.
Next Obligation. exact (@functor_id _ _ (ContextF A Z) X). Defined.
Next Obligation.
  change (first[A; @id (A X); Z] ≈ id).
  rewrite <- (arrow_arr_id A X), arrow_first_arr,
    cross_id, functor_id. reflexivity.
Defined.
Next Obligation. exact (arrow_second_comp A g f Z). Defined.
Next Obligation. exact (arrow_first_comp A g f Z). Defined.

(** Lift the same pure-arrow action into the reindexed category. Objects
    are mapped identically and no additional computation data is stored. *)

(** 将同一纯态射作用提升到重索引后的范畴。对象映射为恒等，不保存额外计算
    数据。 *)

Program Definition ArrowPureF
  : Functor C (ComputationCat A)
  :=
  {|F0 X := X
  ; F1 X Y f := arr[A; f]
  ; functor_fmap_proper X Y := @functor_fmap_proper C K A X Y
  ; functor_id X := arrow_arr_id A X
  ; functor_comp X Y Z g f := arrow_arr_comp A g f
  |}.

(** Pure maps commute with arbitrary computations in both tensor positions.
    The proof reuses the two existing context-naturality laws. *)

(** 纯映射在两个张量位置都与任意计算交换，证明复用已有两种上下文自然性律。 *)

Definition arrow_pure_central {X Y : @Ob C} (f : Hom X Y)
  : @is_central (ComputationCat A) ArrowBinoidal X Y (arr[A; f]).
Proof.
  intros Z W g. split.
  - change (first[A; arr[A; f]; W] ∘ second[A; g; X] ≈
      second[A; g; Y] ∘ first[A; arr[A; f]; Z]).
    rewrite !arrow_first_arr. exact (arrow_second_natural A g f).
  - change (second[A; arr[A; f]; W] ∘ first[A; g; X] ≈
      first[A; g; Y] ∘ second[A; arr[A; f]; Z]).
    rewrite !arrow_second_arr. exact (arrow_first_natural A g f).
Defined.

(** Generic left-before-right sequencing is exactly the existing Arrow
    split, in the specified computation equality. *)

(** 一般先左后右组合在指定计算相等下恰好是已有 Arrow split。 *)

Lemma arrow_binoidal_sequence {X Y Z W : @Ob C}
    (f : Hom (A X) (A Y)) (g : Hom (A Z) (A W))
  : @binoidal_sequence (ComputationCat A) ArrowBinoidal X Y Z W f g
      ≈ f ***[A] g.
Proof. reflexivity. Qed.

End Cartesian.
