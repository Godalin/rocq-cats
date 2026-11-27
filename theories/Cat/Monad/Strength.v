From Cats Require Export
  Cat.Monad.Extension
  Cat.Monoidal.Strength.

Local Open Scope monoidal_scope.
Local Open Scope monad_fct_scope.
Local Open Scope ob_scope.

(** * Strong Monads

    The underlying ordinary monad is unchanged. Chosen tensorial strength
    must preserve its unit and multiplication; no commutativity is imposed. *)

(** * 强 Monad

    底层普通 Monad 保持不变。选定张量强度必须保持其单位和乘法，不要求交换性。 *)

Minks.Mixin IsStrongMonad {C : Cat}
    `{MC : !HasMonoidal C} (T : Fct C C)
  extends @HasMonad C T, @HasStrength C MC T
  :=
  { strongmonad_unit (X Y : C)
    : st[X; Y] ∘ (id ⊗ η[T] Y)
      ≈ η[T] (X ⊗ Y)
  ; strongmonad_mul (X Y : C)
    : st[X; Y] ∘ (id ⊗ μ[T] Y)
      ≈ μ[T] (X ⊗ Y) ∘ fmap T st[X; Y] ∘ st[X; T Y]
  }.

Local Close Scope monad_fct_scope.
Local Open Scope monad_scope.

(** Extend the same monad with a strength compatible with its operations. *)

(** 在同一个 Monad 上选取与其运算相容的强度。 *)

Minks.Struct StrongMonad (C : Cat)
    `{MC : !HasMonoidal C}
  extends Monad C
  with  hasStrength as hasStrength
        : HasStrength [C, MC, carrier],
        isStrongMonad
        : IsStrongMonad
          [C, MC, carrier, hasMonad, hasStrength].

Arguments StrongMonadOfMonad {_ _} _ _ _.
Arguments StrongMonadToMonad {_ _} _.
Arguments hasStrength {_ _} _.
Arguments strongmonad_unit {_ _} _ {_ _ _} _ _.
Arguments strongmonad_mul {_ _} _ {_ _ _} _ _.

(** ** Extending with Tensorial Strength

    Fix a StrongMonad over the selected monoidal structure. Derive contextual
    extension and sequencing laws from its strength and multiplication. *)

(** ** 通过张量强度扩张

    固定选定幺半结构上的 StrongMonad，从其强度与乘法导出上下文扩张及顺序组合定律。 *)

Section StrongExtension.
Context {C : Cat}
  `{MC : !HasMonoidal C} (M : StrongMonad C).

(** Extend an effectful arrow while retaining an ordinary tensor context. *)

(** 保留通常张量上下文，扩张带效应箭头。 *)

Definition strong_extend {X Y Z : C}
    (f : Hom (X ⊗ Y) (M Z))
  : Hom (X ⊗ M Y) (M Z)
  := kleisli_extend M f ∘ st[X; Y].

(** Contextual extension preserves the specified arrow equality. *)

(** 上下文扩张保持指定态射相等。 *)

Global Instance strong_extend_proper {X Y Z : C}
  : Proper (HomEq ==> HomEq) (@strong_extend X Y Z).
Proof.
  intros f g H. unfold strong_extend.
  rewrite H. reflexivity.
Qed.

(** Pure inputs cancel extension, leaving the original contextual arrow. *)

(** 纯输入消去扩张，留下原上下文箭头。 *)

Lemma strong_extend_pure {X Y Z : C}
    (f : Hom (X ⊗ Y) (M Z))
  : strong_extend f ∘ (id ⊗ η[M] Y) ≈ f.
Proof.
  unfold strong_extend.
  rewrite comp_assoc, (strongmonad_unit M X Y).
  apply kleisli_extend_pure.
Qed.

(** A pure output operation can be mapped after strength. *)

(** 纯输出运算可在强度之后映射。 *)

Lemma strong_extend_return {X Y Z : C}
    (f : Hom (X ⊗ Y) Z)
  : strong_extend (η[M] Z ∘ f)
    ≈ fmap M f ∘ st[X; Y].
Proof.
  unfold strong_extend.
  rewrite kleisli_extend_pre,
    kleisli_extend_unit,
    comp_id_l.
  reflexivity.
Qed.

(** Ordinary result mapping commutes with contextual extension. *)

(** 通常结果映射与上下文扩张交换。 *)

Lemma strong_extend_post {X Y Z W : C}
    (f : Hom (X ⊗ Y) (M Z)) (g : Hom Z W)
  : fmap M g ∘ strong_extend f
    ≈ strong_extend (fmap M g ∘ f).
Proof.
  unfold strong_extend.
  rewrite <- comp_assoc, kleisli_extend_post.
  reflexivity.
Qed.

(** Ordinary substitution in both tensor factors commutes with extension. *)

(** 两个张量因子中的通常代入与扩张交换。 *)

Lemma strong_extend_pre {X X' Y Y' Z : C}
    (f : Hom (X' ⊗ Y') (M Z))
    (g : Hom X X') (h : Hom Y Y')
  : strong_extend f ∘ (g ⊗ fmap M h)
    ≈ strong_extend (f ∘ (g ⊗ h)).
Proof.
  unfold strong_extend. rewrite comp_assoc,
    (strength_natural g h), <- comp_assoc,
    <- kleisli_extend_pre. reflexivity.
Qed.

(** Strength also commutes with Kleisli extension. This is the reusable
    compatibility used for nested contextual computations. *)

(** 强度也与 Kleisli 扩张交换；此可复用相容性用于嵌套上下文计算。 *)

Lemma strength_kleisli {X Y Z : C}
    (f : Hom Y (M Z))
  : st[X; Z] ∘ (id ⊗ kleisli_extend M f)
    ≈ kleisli_extend M (st[X; Z] ∘ (id ⊗ f))
      ∘ st[X; Y].
Proof.
  unfold kleisli_extend.
  transitivity ((st[X; Z] ∘ (id ⊗ μ[M] Z)) ∘ (id ⊗ fmap M f)).
  - rewrite comp_assoc,
      <- (tensor_map_comp (id[X]) id (μ[M] Z) (fmap M f)), comp_id_l.
    reflexivity.
  - rewrite (strongmonad_mul M X Z), !comp_assoc,
      (strength_natural (id[X]) f),
      (fmap_comp st[X; Z] (id[X] ⊗ f)), <- !comp_assoc. reflexivity.
Qed.

(** Nested contexts compose by the chosen associator. Effects keep their
    original order; this is not an interchange law for two effects. *)

(** 嵌套上下文按选定结合子复合。效应保留原次序；这不是两个效应的交换律。 *)

Lemma strong_extend_assoc {X Y Z U V : C}
    (f : Hom (Y ⊗ Z) (M U))
    (g : Hom (X ⊗ U) (M V))
  : strong_extend g ∘ (id ⊗ strong_extend f) ∘ α[X; Y; M Z]
    ≈ strong_extend (strong_extend g ∘ (id ⊗ f) ∘ α[X; Y; Z]).
Proof.
  unfold strong_extend.
  transitivity (kleisli_extend M g
    ∘ (st[X; U] ∘ (id ⊗ kleisli_extend M f))
    ∘ (id ⊗ st[Y; Z]) ∘ α[X; Y; M Z]).
  - assert (K : ((id[X]) ⊗ (kleisli_extend M f ∘ st[Y; Z]))
      ≈ (id ⊗ kleisli_extend M f) ∘ (id ⊗ st[Y; Z])).
    { rewrite <- tensor_map_comp, comp_id_l. reflexivity. }
    rewrite K, !comp_assoc. reflexivity.
  - rewrite (strength_kleisli f), <- !comp_assoc,
      <- (kleisli_extend_assoc M
        (st[X; U] ∘ (id ⊗ f)) g), !comp_assoc,
      <- (comp_assoc _ _ α[X; Y; M Z]),
      <- (strength_assoc (hasStrength M) X Y Z),
      <- !comp_assoc, <- kleisli_extend_pre, !comp_assoc. reflexivity.
Qed.

End StrongExtension.
