From Cats Require Export
  Cat.Monoidal.Magmoidal
  Cat.Monoidal.Associator.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Semigroupal Categories

    A fixed tensor with interchange and a coherent associator
    supplies joint naturality and the pentagon without units. *)

(** * 半群张量

    固定张量的交换律及相干结合子给出联合自然性和五边形，无需单位。 *)

(** Add a chosen associator to the tensor with interchange. *)

(** 为带交换律的张量选取结合子。 *)

Minks.Struct SemigroupalCat
  extends MagmoidalCat
  with  associator : HasTensorAssoc.

(** Fix the tensor interchange and a chosen associator. Separate
    naturality and the pentagon give coherence for the joint bifunctor. *)

(** 固定张量的交换律及选定结合子。分别自然性与五边形给出联合双函子的相干性。 *)

Section Associativity.
Context {C : Cat}
  `{BC : !HasBinoidal C} `{IM : !@IsMagmoidal C BC}
  `{AC : !@HasTensorAssoc C BC}.

(** The inherited pentagon expressed with the derived bimap. *)

(** 用导出的二元映射表述继承的五边形。 *)

Lemma tensor_pentagon (W X Y Z : @Ob C)
  : α[W; X; Y ⊗ Z] ∘ α[W ⊗ X; Y; Z]
    ≈ (id ⊗ α[X; Y; Z])
      ∘ (α[W; X ⊗ Y; Z] ∘ (α[W; X; Y] ⊗ id)).
Proof.
  unfold tensor_map.
  rewrite tensor_sequence_left, tensor_sequence_right.
  apply tensor_assoc_pentagon.
Qed.

End Associativity.
