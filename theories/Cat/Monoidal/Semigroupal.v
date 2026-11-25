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

(** The left bracketing of a tensor on triples. *)

(** 三个对象上的左括号张量函子。 *)

Definition Tensor3LF {C : Cat} (T : Fct (C ×C C) C)
  : Fct ((C ×C C) ×C C) C
  := T ∘F (T ×F IdF).

(** The right bracketing, on the same triple-product source. *)

(** 在同一个三重乘积来源上的右括号张量函子。 *)

Program Definition Tensor3RF {C : Cat} (T : Fct (C ×C C) C)
  : Fct ((C ×C C) ×C C) C
  :=
  {|fobj p := T (fst (fst p), T (snd (fst p), snd p))
  ; fmap p q f := fmap T
      (X := (fst (fst p), T (snd (fst p), snd p)))
      (Y := (fst (fst q), T (snd (fst q), snd q)))
      (fst (fst f), fmap T
        (X := (snd (fst p), snd p)) (Y := (snd (fst q), snd q))
        (snd (fst f), snd f))
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros [[f g] h] [[f' g'] h'] [[Hf Hg] Hh]. cbn.
  apply fmap_proper. split; [exact Hf |].
  apply (fmap_proper (IsFct := isFct T)). split; assumption.
Qed.
Next Obligation.
  transitivity (fmap T
    (X := (fst (fst X), T (snd (fst X), snd X)))
    (Y := (fst (fst X), T (snd (fst X), snd X))) (id, id)).
  - apply fmap_proper. split; [reflexivity |].
    exact (fmap_id (IsFct := isFct T) (X := (snd (fst X), snd X))).
  - exact (fmap_id (IsFct := isFct T)
      (X := (fst (fst X), T (snd (fst X), snd X)))).
Qed.
Next Obligation.
  etransitivity; [| apply fmap_comp].
  apply fmap_proper. split; [reflexivity |].
  exact (fmap_comp (IsFct := isFct T)
    (X := (snd (fst X), snd X)) (Y := (snd (fst Y), snd Y))
    (Z := (snd (fst Z), snd Z))
    (snd (fst f), snd f) (snd (fst g), snd g)).
Qed.

(** Display the two bracketings when the object argument is a triple.
    Use application precedence to preserve grouping inside larger terms. *)

(** 当对象参数是三元组时显示两种括号排列。采用函数应用的优先级，
    使它们作为更大表达式的参数时保留括号。 *)

#[warnings="-postfix-notation-not-level-1"]
Notation "T ( T ( X , Y ) , Z )"
  := (fobj (Tensor3LF T) ((X, Y), Z))
  (at level 10, T at level 9, only printing,
    format "T  ( T  ( X ,  Y ) ,  Z )")
  : monoidal_scope.
#[warnings="-postfix-notation-not-level-1"]
Notation "T ( X , T ( Y , Z ) )" :=
  (fobj (Tensor3RF T) ((X, Y), Z))
  (at level 10, T at level 9, only printing,
    format "T  ( X ,  T  ( Y ,  Z ) )")
  : monoidal_scope.

(** Fix the tensor interchange and a chosen associator. Separate
    naturality and the pentagon give coherence for the joint bifunctor. *)

(** 固定张量的交换律及选定结合子。分别自然性与五边形给出联合双函子的相干性。 *)

Section Associativity.
Context {C : Cat}
  `{BC : !HasBinoidal C} `{IM : !@IsMagmoidal C BC}
  `{AC : !@HasTensorAssoc C BC}.

(** Package derived joint naturality with the inherited associator. *)

(** 将导出的联合自然性与继承结合子打包。 *)

Local Program Definition TensorAssociatorN
  : Tensor3LF (tensorF IM) ⇒ Tensor3RF (tensorF IM)
  :=
  {|nt p := α[fst (fst p); snd (fst p); snd p]
  |}.
Next Obligation.
  destruct X as [[x y] z], Y as [[x' y'] z'], f as [[f g] h].
  apply tensor_assoc_sequence_natural.
Qed.

(** The natural isomorphism retains the same component inverses. *)

(** 自然同构保留相同的分量逆。 *)

Definition TensorAssocIsoN
  : Tensor3LF (tensorF IM) ≅N Tensor3RF (tensorF IM)
  := (TensorAssociatorN;
      λ p, (tensor_assoc (fst (fst p)) (snd (fst p)) (snd p)).2).

(** The inherited pentagon expressed with the derived bimap. *)

(** 用导出的二元映射表述继承的五边形。 *)

Lemma tensor_pentagon (W X Y Z : C)
  : α[W; X; Y ⊗ Z] ∘ α[W ⊗ X; Y; Z]
    ≈ (id ⊗ α[X; Y; Z])
      ∘ (α[W; X ⊗ Y; Z] ∘ (α[W; X; Y] ⊗ id)).
Proof.
  unfold tensor_map.
  rewrite tensor_sequence_left, tensor_sequence_right.
  apply tensor_assoc_pentagon.
Qed.

End Associativity.
