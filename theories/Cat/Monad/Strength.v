From Cats Require Export
  Cat.Monad.Extension
  Cat.Monoidal.Strength.

Local Open Scope monoidal_scope.
Local Open Scope monad_scope.

(** * Strong Monads

    The underlying ordinary monad is unchanged. Chosen tensorial strength
    must preserve its unit and multiplication; no commutativity is imposed. *)

(** * 强 Monad

    底层普通 Monad 保持不变。选定张量强度必须保持其单位和乘法，不要求交换性。 *)

Class StrongMonad (C : Cat) (MC : MonoidalCategory C)
  :=
  (** The unique coercion exposes the existing ordinary monad. *)

  (** 唯一强制转换暴露已有普通 Monad。 *)

  { StrongMonadM :> Monad C

  (** Strength is additional chosen structure on that monad's functor. *)

  (** 强度是该 Monad 函子上额外选定的结构。 *)

  ; strongmonad_strength :: HasStrength MC StrongMonadM

  (** A pure effectful input gives the pure tensor pair. *)

  (** 纯的带效应输入给出纯张量配对。 *)

  ; strongmonad_unit (X Y : @Ob C)
    : st[strongmonad_strength; X; Y] ∘
        (@tensor_map C MC _ _ _ _ id (η[StrongMonadM] Y)) ≈
        η[StrongMonadM] (@tensor C MC X Y)

  (** Passing through multiplication agrees with passing through both layers. *)

  (** 穿过乘法，等于依次穿过两层。 *)

  ; strongmonad_mul (X Y : @Ob C)
    : st[strongmonad_strength; X; Y] ∘
        (@tensor_map C MC _ _ _ _ id (μ[StrongMonadM] Y)) ≈
        μ[StrongMonadM] (@tensor C MC X Y) ∘
          fmap StrongMonadM st[strongmonad_strength; X; Y] ∘
          st[strongmonad_strength; X; StrongMonadM Y]
  }.

Arguments StrongMonadM {_ _} _.
Arguments strongmonad_strength {_ _} _.
Arguments strongmonad_unit {_ _} _ _ _.
Arguments strongmonad_mul {_ _} _ _ _.

Section Extension.
Context {C : Cat} `{MC : !MonoidalCategory C} (M : StrongMonad C MC).

(** Extend an effectful arrow while retaining an ordinary tensor context. *)

(** 保留通常张量上下文，扩张带效应箭头。 *)

Definition strong_extend {X Y Z : @Ob C} (f : Hom (X ⊗ Y) (M Z))
  : Hom (X ⊗ M Y) (M Z)
  := kleisli_extend M f ∘ st[strongmonad_strength M; X; Y].

(** Contextual extension preserves the specified arrow equality. *)

(** 上下文扩张保持指定态射相等。 *)

Global Instance strong_extend_proper {X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq) (@strong_extend X Y Z).
Proof. intros f g H. unfold strong_extend. rewrite H. reflexivity. Qed.

(** Pure inputs cancel extension, leaving the original contextual arrow. *)

(** 纯输入消去扩张，留下原上下文箭头。 *)

Lemma strong_extend_pure {X Y Z : @Ob C} (f : Hom (X ⊗ Y) (M Z))
  : strong_extend f ∘ (id ⊗m η[M] Y) ≈ f.
Proof.
  unfold strong_extend. rewrite comp_assoc, (strongmonad_unit M X Y).
  apply kleisli_extend_pure.
Qed.

(** A pure output operation can be mapped after strength. *)

(** 纯输出运算可在强度之后映射。 *)

Lemma strong_extend_return {X Y Z : @Ob C} (f : Hom (X ⊗ Y) Z)
  : strong_extend (η[M] Z ∘ f) ≈
      fmap M f ∘ st[strongmonad_strength M; X; Y].
Proof.
  unfold strong_extend. rewrite kleisli_extend_pre, kleisli_extend_unit,
    comp_id_l. reflexivity.
Qed.

(** Ordinary result mapping commutes with contextual extension. *)

(** 通常结果映射与上下文扩张交换。 *)

Lemma strong_extend_post {X Y Z W : @Ob C}
    (f : Hom (X ⊗ Y) (M Z)) (g : Hom Z W)
  : fmap M g ∘ strong_extend f ≈ strong_extend (fmap M g ∘ f).
Proof.
  unfold strong_extend. rewrite <- comp_assoc, kleisli_extend_post. reflexivity.
Qed.

(** Ordinary substitution in both tensor factors commutes with extension. *)

(** 两个张量因子中的通常代入与扩张交换。 *)

Lemma strong_extend_pre {X X' Y Y' Z : @Ob C}
    (f : Hom (X' ⊗ Y') (M Z)) (g : Hom X X') (h : Hom Y Y')
  : strong_extend f ∘ (g ⊗m fmap M h) ≈
      strong_extend (f ∘ (g ⊗m h)).
Proof.
  unfold strong_extend. rewrite comp_assoc,
    (strength_natural (strongmonad_strength M) g h), <- comp_assoc,
    <- kleisli_extend_pre. reflexivity.
Qed.

(** Strength also commutes with Kleisli extension. This is the reusable
    compatibility used for nested contextual computations. *)

(** 强度也与 Kleisli 扩张交换；此可复用相容性用于嵌套上下文计算。 *)

Lemma strength_kleisli {X Y Z : @Ob C} (f : Hom Y (M Z))
  : st[strongmonad_strength M; X; Z] ∘ (id ⊗m kleisli_extend M f) ≈
      kleisli_extend M
        (st[strongmonad_strength M; X; Z] ∘ (id ⊗m f)) ∘
          st[strongmonad_strength M; X; Y].
Proof.
  unfold kleisli_extend.
  transitivity ((st[strongmonad_strength M; X; Z] ∘
    (id ⊗m μ[M] Z)) ∘ (id ⊗m fmap M f)).
  - rewrite comp_assoc,
      <- (@tensor_map_comp C MC X X X (M Y) (M (M Z)) (M Z)
        id id (μ[M] Z) (fmap M f)), comp_id_l. reflexivity.
  - rewrite (strongmonad_mul M X Z), !comp_assoc,
      (strength_natural (strongmonad_strength M) (@id X) f),
      (@functor_comp C C M _ _ _ st[strongmonad_strength M; X; Z]
        (@tensor_map C MC _ _ _ _ id f)), <- !comp_assoc. reflexivity.
Qed.

(** Nested contexts compose by the chosen associator. Effects keep their
    original order; this is not an interchange law for two effects. *)

(** 嵌套上下文按选定结合子复合。效应保留原次序；这不是两个效应的交换律。 *)

Lemma strong_extend_assoc {X Y Z U V : @Ob C}
    (f : Hom (Y ⊗ Z) (M U)) (g : Hom (X ⊗ U) (M V))
  : strong_extend g ∘ (id ⊗m strong_extend f) ∘ α⊗[X; Y; M Z] ≈
      strong_extend (strong_extend g ∘ (id ⊗m f) ∘ α⊗[X; Y; Z]).
Proof.
  unfold strong_extend.
  transitivity (kleisli_extend M g ∘
    (st[strongmonad_strength M; X; U] ∘ (id ⊗m kleisli_extend M f)) ∘
    (id ⊗m st[strongmonad_strength M; Y; Z]) ∘ α⊗[X; Y; M Z]).
  - assert (K : ((@id X) ⊗m (kleisli_extend M f ∘
        st[strongmonad_strength M; Y; Z])) ≈
        (id ⊗m kleisli_extend M f) ∘
          (id ⊗m st[strongmonad_strength M; Y; Z])).
    { rewrite <- tensor_map_comp, comp_id_l. reflexivity. }
    rewrite K, !comp_assoc. reflexivity.
  - rewrite (strength_kleisli f), <- !comp_assoc,
      <- (kleisli_extend_assoc M
        (st[strongmonad_strength M; X; U] ∘ (id ⊗m f)) g), !comp_assoc,
      <- (comp_assoc st[strongmonad_strength M; X; Y ⊗ Z]
        (id ⊗m st[strongmonad_strength M; Y; Z]) α⊗[X; Y; M Z]),
      <- (strength_assoc (strongmonad_strength M) X Y Z),
      <- !comp_assoc, <- kleisli_extend_pre, !comp_assoc. reflexivity.
Qed.

End Extension.
