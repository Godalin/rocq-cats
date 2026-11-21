From Cats Require Export
  Cat.Monoidal.Center.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Magmoidal Tensor

    Interchange makes the two tensor actions jointly functorial on a
    fixed tensor. The resulting bifunctor needs no associator or unit. *)

(** * 带交换律的张量

    交换律使固定张量的两个作用具有联合函子性。所得双函子无需结合子或单位。 *)

(** Interchange equates the two orders of acting on a fixed tensor. *)

(** 交换律使固定张量作用的两种执行次序相等。 *)

Minks.Mixin IsMagmoidal (C : Cat)
  extends HasBinoidal C
  :=
  { tensor_interchange {X X' Y Y' : C}
      (f : Hom X X') (g : Hom Y Y')
    : (f ⊳ Y') ∘ (X ⊲ g) ≈ (X' ⊲ g) ∘ (f ⊳ Y)
  }.

Arguments tensor_interchange {_ _ _ _ _ _ _} _ _.

(** Add interchange to the tensor actions of one binoidal category. *)

(** 为一个双侧张量范畴的张量作用加入交换律。 *)

Minks.Struct MagmoidalCat
  extends BinoidalCat
  with  interchange as isMagmoidal : IsMagmoidal.

(** Tensor two arrows when the chosen actions satisfy interchange. The
    map computes by the left-then-right order of [tensor_sequence]. *)

(** 当选定作用满足交换律时张量两条态射。映射按照 [tensor_sequence] 先左后右计算。 *)

Definition tensor_map {C : Cat}
    `{BC : !HasBinoidal C}
    `{IM : !@IsMagmoidal C BC}
    {X X' Y Y' : C} (f : Hom X X') (g : Hom Y Y')
  : Hom (X ⊗ Y) (X' ⊗ Y')
  := tensor_sequence f g.

Infix "⊗" := tensor_map
  (at level 41, right associativity)
  : hom_scope.

(** ** Joint Functoriality

    Fix interchange and derive joint functoriality of the selected
    actions using the composition laws for central arrows. *)

(** ** 联合函子性

    固定交换律，利用中心态射的复合定律导出选定作用的联合函子性。 *)

Section JointFunctoriality.
Context {C : Cat}
  `{BC : !HasBinoidal C}
  `{IM : !@IsMagmoidal C BC}.

(** Every arrow is central; interchange equates the two action orders. *)

(** 每条态射都是中心态射；交换律等同两种作用次序。 *)

Definition tensor_arrow_central {X Y : C} (f : Hom X Y)
  : is_central f.
Proof.
  intros Z W g. split.
  - apply tensor_interchange.
  - symmetry. apply tensor_interchange.
Qed.

(** Tensoring respects the specified equality of each arrow. *)

(** 张量保持两条态射各自的指定相等。 *)

Global Instance tensor_map_proper {X X' Y Y' : C}
  : Proper (HomEq ==> HomEq ==> HomEq)
      (@tensor_map C BC IM X X' Y Y').
Proof. apply tensor_sequence_proper. Qed.

(** The joint tensor map preserves identities. *)

(** 联合张量映射保持恒等态射。 *)

Lemma tensor_map_id (X Y : C)
  : id[X] ⊗ id[Y] ≈ id[X ⊗ Y].
Proof. apply tensor_sequence_id. Qed.

(** Interchange makes ordered tensoring jointly functorial. *)

(** 交换律使有序张量联合具有函子性。 *)

Lemma tensor_map_comp {X X' X'' Y Y' Y'' : C}
    (f' : Hom X' X'') (f : Hom X X')
    (g' : Hom Y' Y'') (g : Hom Y Y')
  : (f' ∘ f) ⊗ (g' ∘ g) ≈ (f' ⊗ g') ∘ (f ⊗ g).
Proof.
  exact (central_sequence_comp f' f g' g
    (tensor_arrow_central f')).
Qed.

End JointFunctoriality.

(** The tensor bifunctor is computed, not stored as another choice.
    Pair projections preserve reduction on an undestructed input pair. *)

(** 张量双函子通过计算得到，不另作选择。对投影保留未拆解输入对上的归约。 *)

Program Definition tensorF {C : Cat}
    `{BC : !HasBinoidal C} `{IM : !@IsMagmoidal C BC}
  : Fct (C ×C C) C
  :=
  {|fobj p := fst p ⊗ snd p
  ; fmap p q f := (fst f ⊗ snd f)%hom
  ; isFct :=
    {|fmap_proper := _
    ; fmap_id := _
    ; fmap_comp := _
    |}
  |}.
Next Obligation.
  intros [f1 f2] [g1 g2] [H1 H2].
  apply tensor_map_proper; assumption.
Qed.
Next Obligation. apply tensor_map_id. Qed.
Next Obligation. apply tensor_map_comp. Qed.

Arguments tensorF {_ _} _.
