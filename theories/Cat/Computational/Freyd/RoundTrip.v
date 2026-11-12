From Cats Require Export
  Cat.Computational.Freyd.Arrow
  Cat.Computational.Arrow.Freyd.
From Cats Require Import
  Cat.CatCat.

Local Open Scope computation_scope.

(** * Round Trips for Computational Arrows and Freyd Categories

    Compare operations in specified hom equality and functors by natural
    isomorphisms. The Freyd-side equivalence concerns the actual indexed
    computation categories, with explicit structural boundaries. It makes
    no assertion about unused ambient objects or equality of law records. *)

(** * 计算 Arrow 与 Freyd 范畴的往返

    运算按指定 Hom 相等比较，函子通过自然同构比较。Freyd 方向的等价涉及
    实际索引计算范畴，并使用显式结构边界；不主张未使用的环境对象或定律
    记录相等。 *)

(** First fix a computational Arrow with selected cartesian values. Compare
    the pure functor and context action after its Freyd round trip. *)

(** 首先固定具有选定笛卡尔值的计算 Arrow，比较经 Freyd 往返后的纯函子与上下文作用。 *)

Section ArrowRoundTrip.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Returning through Freyd reindexes the same computation hom-sets. *)

(** 经 Freyd 返回时重索引同一计算 Hom 广集。 *)

Definition ArrowFreydRoundTrip
  : Arrow C (ComputationCat A) (@CartesianMonoidal C HT HP)
  := FreydArrow (ArrowFreyd A).

(** Pure maps are unchanged on every hom-set. *)

(** 每个 Hom 广集上的纯映射保持不变。 *)

Lemma arrow_freyd_round_trip_arr {X Y : @Ob C} (f : Hom X Y)
  : arr[ArrowFreydRoundTrip; f] ≈ arr[A; f].
Proof. reflexivity. Qed.

(** Context operations return up to the specified computation equality. *)

(** 上下文运算在指定计算相等下恢复。 *)

Lemma arrow_freyd_round_trip_context {X Y : @Ob C} (Z : @Ob C)
    (f : Hom (A X) (A Y))
  : context[ArrowFreydRoundTrip; Z; f] ≈ context[A; Z; f].
Proof.
  pose proof (freyd_context_boundary (ArrowFreyd A) Z f) as H.
  change (@HomEq K _ _
    (@Cats.Cat.Core.comp K _ _ _ (@Cats.Cat.Core.id K _)
      (freyd_context (ArrowFreyd A) Z f))
    (@Cats.Cat.Core.comp K _ _ _ (context[A; Z; f])
      (@Cats.Cat.Core.id K _))) in H.
  rewrite (@comp_id_l K), (@comp_id_r K) in H. exact H.
Qed.

(** Including the indexed computation category recovers the original pure
    functor by an actual natural isomorphism with identity components. *)

(** 嵌入索引计算范畴后，以具有恒等分量的实际自然同构恢复原纯函子。 *)

Definition ArrowFreydRoundTripIso
  : (InducedInclusionF (@Ob C) A ∘F ArrowFreydRoundTrip) ≅N A
  := InducedFactorIso A.

End ArrowRoundTrip.

(** ** Returning to the Freyd Computation Structure

    Fix a Freyd structure between the value and ambient categories. Compare
    its returned value-indexed computation category and all structural boundaries. *)

(** ** 返回 Freyd 计算结构

    固定值与环境范畴间的 Freyd 结构，比较返回的值索引计算范畴及全部结构边界。 *)

Section FreydRoundTrip.
Context {C K : Cat} (F : FreydCat C K).
Let D
  : Cat
  := FreydComputations F.
Let CC
  : CartesianCat C
  := @hasCartesian C K F.
Local Existing Instance CC.
Let SP
  : SymmetricPremonoidalCat D
  := @hasSymmetricPremonoidal C K F.
Local Existing Instance SP.

(** The returned Freyd structure uses value products as literal tensors. *)

(** 返回的 Freyd 结构以值积为直接张量。 *)

Definition FreydRoundTrip
  : FreydCat C D
  := ArrowFreyd (FreydArrow F).

(** The comparison includes the second indexing, acting identically on
    both value objects and computational arrows. *)

(** 比较嵌入第二次索引，在值对象与计算态射上均恒等作用。 *)

Definition FreydRoundTripToF
  : Functor (FreydComputations FreydRoundTrip) D
  := InducedInclusionF (@Ob C) (FreydArrow F).

(** The inverse also retains every computation. *)

(** 反向函子同样保留每个计算。 *)

Program Definition FreydRoundTripFromF
  : Functor D (FreydComputations FreydRoundTrip)
  :=
  {|F0 X := X
  ; F1 X Y f := f
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** One composite is compared to identity by identity components. *)

(** 一个复合通过恒等分量与恒等函子比较。 *)

Program Definition FreydRoundTripToN
  : (FreydRoundTripToF ∘F FreydRoundTripFromF) ⇒ (@IdF D)
  :=
  {|nt X := id
  |}.
Next Obligation.
  transitivity f; [exact (@comp_id_l D X Y f) |
    symmetry; exact (@comp_id_r D X Y f)].
Defined.

(** The other composite has the same identity comparison. *)

(** 另一个复合具有同样的恒等比较。 *)

Program Definition FreydRoundTripFromN
  : (FreydRoundTripFromF ∘F FreydRoundTripToF) ⇒
      (@IdF (FreydComputations FreydRoundTrip))
  :=
  {|nt X := id
  |}.
Next Obligation.
  transitivity f;
    [exact (@comp_id_l (FreydComputations FreydRoundTrip) X Y f) |
      symmetry; exact (@comp_id_r (FreydComputations FreydRoundTrip) X Y f)].
Defined.

(** Both directions form a categorical equivalence, retaining the inverse
    functor and both natural-isomorphism witnesses. *)

(** 两个方向构成范畴等价，保留逆函子及两个自然同构见证。 *)

Definition FreydRoundTripEq
  : FreydComputations FreydRoundTrip ≃C D.
Proof.
  exists FreydRoundTripToF, FreydRoundTripFromF. split.
  - exists FreydRoundTripFromN. intro X.
    exists id. split;
      exact (@comp_id_l (FreydComputations FreydRoundTrip) X X id).
  - exists FreydRoundTripToN. intro X.
    exists id. split; exact (@comp_id_l D X X id).
Defined.

(** The comparison commutes with the pure inclusion up to natural
    isomorphism, rather than equality of functor records. *)

(** 比较在自然同构意义下与纯嵌入相容，不要求函子记录相等。 *)

Definition FreydRoundTripPureIso
  : (FreydRoundTripToF ∘F FreydPureF FreydRoundTrip) ≅N FreydPureF F
  := InducedFactorIso (FreydPureF F).

(** The left action is preserved across the original tensor boundary. *)

(** 跨原张量边界保持左作用。 *)

Lemma freyd_round_trip_left {X Y : @Ob C} (Z : @Ob C)
    (f : (@Hom D) X Y)
  : (FreydTensorIso F Z Y).1 ∘
      fmap FreydRoundTripToF
        (@binoidal_left (FreydComputations FreydRoundTrip)
          (@hasSymmetricPremonoidal _ _ FreydRoundTrip) X Y Z f) ≈
      (@binoidal_left D SP X Y Z f) ∘ (FreydTensorIso F Z X).1.
Proof. exact (freyd_context_boundary F Z f). Qed.

(** Pure exchange crosses the same tensor boundaries as every other
    preserved structural map. *)

(** 纯交换跨越与其他保持结构映射相同的张量边界。 *)

Lemma freyd_exchange_boundary (X Y : @Ob C)
  : (FreydTensorIso F Y X).1 ∘
      fmap (FreydPureF F) (⟨π2, π1⟩ : Hom (X × Y) (Y × X)) ≈
      (@premonoidal_symmetry D SP X Y) ∘ (FreydTensorIso F X Y).1.
Proof. exact (@freyd_symmetry C K F X Y). Qed.

(** The right action is also preserved, using exchange and the already
    established left boundary square. No effect interchange is needed. *)

(** 利用交换及已有左边界方块，也保持右作用；无需效应交换律。 *)

Lemma freyd_round_trip_right {X Y : @Ob C} (Z : @Ob C)
    (f : (@Hom D) X Y)
  : (FreydTensorIso F Y Z).1 ∘
      fmap FreydRoundTripToF
        (@binoidal_right (FreydComputations FreydRoundTrip)
          (@hasSymmetricPremonoidal _ _ FreydRoundTrip) X Y Z f) ≈
      (@binoidal_right D SP X Y Z f) ∘ (FreydTensorIso F X Z).1.
Proof.
  change ((FreydTensorIso F Y Z).1 ∘
    (fmap (FreydPureF F) (⟨π2, π1⟩ : Hom (Z × Y) (Y × Z)) ∘
      freyd_context F Z f ∘
      fmap (FreydPureF F) (⟨π2, π1⟩ : Hom (X × Z) (Z × X))) ≈
    (@binoidal_right D SP X Y Z f) ∘ (FreydTensorIso F X Z).1).
  etransitivity.
  - exact (@comp_square D _ _ _ _ _ _
      (FreydTensorIso F X Z).1 (FreydTensorIso F Z X).1
      (FreydTensorIso F Y Z).1
      (fmap (FreydPureF F) (⟨π2, π1⟩ : Hom (X × Z) (Z × X)))
      (fmap (FreydPureF F) (⟨π2, π1⟩ : Hom (Z × Y) (Y × Z)) ∘
        freyd_context F Z f)
      (@premonoidal_symmetry D SP X Z)
      ((@premonoidal_symmetry D SP Z Y) ∘ (@binoidal_left D SP X Y Z f))
      (freyd_exchange_boundary X Z)
      (@comp_square D _ _ _ _ _ _
        (FreydTensorIso F Z X).1 (FreydTensorIso F Z Y).1
        (FreydTensorIso F Y Z).1
        (freyd_context F Z f)
        (fmap (FreydPureF F) (⟨π2, π1⟩ : Hom (Z × Y) (Y × Z)))
        (@binoidal_left D SP X Y Z f) (@premonoidal_symmetry D SP Z Y)
        (freyd_context_boundary F Z f) (freyd_exchange_boundary Z Y))).
  - apply (@comp_proper D); [| reflexivity].
    etransitivity.
    + exact (@comp_assoc D _ _ _ _ (@premonoidal_symmetry D SP Z Y)
        (@binoidal_left D SP X Y Z f) (@premonoidal_symmetry D SP X Z)).
    + symmetry. exact (@premonoidal_right_symmetry D SP X Y Z f).
Qed.

(** Left-unit preservation uses the original chosen unit boundary. *)

(** 左单位保持性使用原选定单位边界。 *)

Lemma freyd_round_trip_unit_l (X : @Ob C)
  : fmap FreydRoundTripToF
      (@premonoidal_left_unitor (FreydComputations FreydRoundTrip)
        (@hasSymmetricPremonoidal _ _ FreydRoundTrip) X).1 ≈
      (@premonoidal_left_unitor D SP X).1 ∘
        (FreydContextBoundary F (@freyd_unit_object C K F) X).1.
Proof. exact (@freyd_unit_l C K F X). Qed.

(** Right-unit preservation retains the specified tensor and unit path. *)

(** 右单位保持性保留指定张量及单位路径。 *)

Lemma freyd_round_trip_unit_r (X : @Ob C)
  : fmap FreydRoundTripToF
      (@premonoidal_right_unitor (FreydComputations FreydRoundTrip)
        (@hasSymmetricPremonoidal _ _ FreydRoundTrip) X).1 ≈
      (@premonoidal_right_unitor D SP X).1 ∘
        @eq_to_hom D _ _
          (eq_trans (@freyd_tensor_objects C K F X (@Term C hasTerminal))
            (f_equal (λ Q, @binoidal_tensor D SP X Q)
              (@freyd_unit_object C K F))).
Proof. exact (@freyd_unit_r C K F X). Qed.

(** Associators are preserved across both nested tensor boundaries. *)

(** 跨两个嵌套张量边界保持结合子。 *)

Lemma freyd_round_trip_assoc (X Y Z : @Ob C)
  : (FreydNestedBoundary F X Y Z).1 ∘
      fmap FreydRoundTripToF
        (@premonoidal_associator (FreydComputations FreydRoundTrip)
          (@hasSymmetricPremonoidal _ _ FreydRoundTrip) X Y Z).1 ≈
      (@premonoidal_associator D SP X Y Z).1 ∘
        (FreydContextBoundary F (@freyd_tensor_objects C K F X Y) Z).1.
Proof. exact (@freyd_assoc C K F X Y Z). Qed.

(** Symmetry is preserved across the original selected tensor boundaries. *)

(** 跨原选定张量边界保持对称性。 *)

Lemma freyd_round_trip_symmetry (X Y : @Ob C)
  : (FreydTensorIso F Y X).1 ∘
      fmap FreydRoundTripToF
        (@premonoidal_symmetry (FreydComputations FreydRoundTrip)
          (@hasSymmetricPremonoidal _ _ FreydRoundTrip) X Y) ≈
      (@premonoidal_symmetry D SP X Y) ∘ (FreydTensorIso F X Y).1.
Proof. exact (@freyd_symmetry C K F X Y). Qed.

End FreydRoundTrip.
