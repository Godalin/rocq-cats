From Cats Require Export
  Cat.Computational.Arrow.Core
  Cat.Monad.Kleisli
  Cat.Monad.Strength.

Local Open Scope monoidal_scope.
Local Open Scope monad_scope.
Local Open Scope computation_scope.

(** * Kleisli Computation with Monoidal Contexts

    The construction uses the specified tensorial strength directly.
    There is no product, symmetry or commutativity assumption. *)

(** * 带幺半上下文的 Kleisli 计算

    构造直接使用指定张量强度，不假定积、对称性或交换性。 *)

Section Kleisli.
Context {C : Cat} `{MC : !MonoidalCategory C} (M : StrongMonad C MC).

(** Carry the ordinary left context through the computation's result. *)

(** 将通常左上下文穿过计算结果。 *)

Definition kleisli_context {X Y : @Ob C} (Z : @Ob C) (f : Hom X (M Y))
  : Hom (Z ⊗ X) (M (Z ⊗ Y))
  := st[hasStrength M; Z; Y] ∘ (id ⊗m f).

(** Specified equality of computations is preserved. *)

(** 保持计算的指定相等。 *)

Global Instance kleisli_context_proper {X Y : @Ob C} (Z : @Ob C)
  : Proper (HomEq ==> HomEq) (@kleisli_context X Y Z).
Proof. intros f g H. unfold kleisli_context. rewrite H. reflexivity. Qed.

(** Strength compatibility gives a lawful Arrow over the monoidal base,
    keeping the existing ordinary Kleisli category and pure-arrow functor. *)

(** 强度相容性给出幺半基底上的带定律 Arrow，保留已有普通 Kleisli 范畴及纯
    箭头函子。 *)

Program Definition KleisliArrow
  : Arrow C (KleisliCat M) MC
  :=
  {|ArrowF := KleisliPureF M
  ; arrow_context X Y Z f := kleisli_context Z f
  ; arrow_context_proper X Y Z := kleisli_context_proper Z
  |}.
Next Obligation.
  change (kleisli_context Z (return[M; f]) ≈ return[M; id ⊗m f]).
  unfold kleisli_context, monad_return.
  transitivity ((st[hasStrength M; Z; Y] ∘ (id ⊗m η[M] Y)) ∘
    (id ⊗m f)).
  - rewrite comp_assoc. apply comp_proper; [reflexivity |].
    pose proof (@tensor_map_comp C MC Z Z Z X Y (M Y)
      id id (η[M] Y) f) as H.
    rewrite comp_id_l in H. exact H.
  - rewrite (strongmonad_unit M Z Y). reflexivity.
Defined.
Next Obligation.
  change ((@Hom C) X (M Y)) in f.
  change ((@Hom C) Y (M W)) in g.
  change (kleisli_context Z (g ∘K[M] f) ≈
    kleisli_context Z g ∘K[M] kleisli_context Z f).
  unfold kleisli_context, kleisli_comp.
  transitivity ((st[hasStrength M; Z; W] ∘
    (id ⊗m kleisli_extend M g)) ∘ (id ⊗m f)).
  - rewrite comp_assoc. apply comp_proper; [reflexivity |].
    pose proof (@tensor_map_comp C MC Z Z Z X (M Y) (M W)
      id id (kleisli_extend M g) f) as H.
    rewrite comp_id_l in H. exact H.
  - rewrite (strength_kleisli M g), !comp_assoc. reflexivity.
Defined.
Next Obligation.
  change ((@Hom C) X (M Y)) in f.
  change (return[M; h ⊗m id] ∘K[M] kleisli_context Z f ≈
    kleisli_context W f ∘K[M] return[M; h ⊗m id]).
  rewrite kleisli_comp_pure_l, kleisli_comp_pure_r.
  unfold kleisli_context.
  rewrite <- comp_assoc, <- (strength_natural (hasStrength M) h (@id Y)),
    functor_id, !comp_assoc.
  apply comp_proper; [reflexivity |].
  transitivity (h ⊗m f).
  - pose proof (@tensor_map_comp C MC Z Z W X (M Y) (M Y)
      h id id f) as H.
    rewrite comp_id_l, comp_id_r in H. symmetry. exact H.
  - pose proof (@tensor_map_comp C MC Z W W X X (M Y)
      id h f id) as H.
    rewrite comp_id_l, comp_id_r in H. exact H.
Defined.
Next Obligation.
  change ((@Hom C) X (M Y)) in f.
  change (return[M; λ⊗[Y]] ∘K[M] kleisli_context (I⊗[MC]) f ≈
    f ∘K[M] return[M; λ⊗[X]]).
  rewrite kleisli_comp_pure_l, kleisli_comp_pure_r.
  unfold kleisli_context. rewrite <- comp_assoc,
    (strength_unit (hasStrength M) Y). apply tensor_unit_l_natural.
Defined.
Next Obligation.
  change ((@Hom C) X (M Y)) in f.
  change (return[M; α⊗[Z; W; Y]] ∘K[M] kleisli_context (Z ⊗ W) f ≈
    kleisli_context Z (kleisli_context W f) ∘K[M]
      return[M; α⊗[Z; W; X]]).
  rewrite kleisli_comp_pure_l, kleisli_comp_pure_r.
  unfold kleisli_context.
  rewrite <- comp_assoc, (strength_assoc (hasStrength M) Z W Y).
  pose proof (@tensor_map_comp C MC Z Z Z
    (W ⊗ X) (W ⊗ M Y) (M (W ⊗ Y)) id id
    st[hasStrength M; W; Y] (id ⊗m f)) as Ht.
  rewrite comp_id_l in Ht.
  pose proof (@tensor_assoc_natural C MC Z Z W W X (M Y)
    id id f) as Ha.
  rewrite tensor_map_id in Ha.
  rewrite Ht, !comp_assoc.
  rewrite Ha. repeat rewrite comp_assoc. reflexivity.
Defined.

End Kleisli.
