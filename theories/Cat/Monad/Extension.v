From Cats Require Export
  Cat.Monad.Core.

Local Open Scope monad_scope.

(** * Kleisli Extension

    Extend an effectful arrow using the existing monad multiplication.
    These lemmas require no products, strength or closed structure. *)

(** * Kleisli 扩张

    用已有 Monad 乘法扩张带效应箭头。这些引理不要求积、强度或闭结构。 *)

Section Extension.
Context {C : Cat} (M : Monad C).

(** Extend a computation from ordinary inputs to monadic inputs. *)

(** 将通常输入上的计算扩张到 Monad 输入。 *)

Definition kleisli_extend {X Y : @Ob C} (f : Hom X (M Y))
  : Hom (M X) (M Y)
  := μ[M] Y ∘ fmap M f.

(** Extension preserves the specified equality of computations. *)

(** 扩张保持计算的指定相等。 *)

Global Instance kleisli_extend_proper {X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@kleisli_extend X Y).
Proof. intros f g H. unfold kleisli_extend. rewrite H. reflexivity. Qed.

(** Extending return leaves the monadic input unchanged. *)

(** 扩张返回运算，保持 Monad 输入不变。 *)

Lemma kleisli_extend_unit (X : @Ob C)
  : kleisli_extend (η[M] X) ≈ id.
Proof. exact (monad_unit_r_component M X). Qed.

(** Extending after a pure input evaluates the original computation. *)

(** 在纯输入之后扩张，求得原计算。 *)

Lemma kleisli_extend_pure {X Y : @Ob C} (f : Hom X (M Y))
  : kleisli_extend f ∘ η[M] X ≈ f.
Proof.
  unfold kleisli_extend. rewrite comp_assoc, <- (nt_naturality (η[M]) f),
    <- comp_assoc, (monad_unit_l_component M Y), comp_id_l. reflexivity.
Qed.

(** Ordinary input substitution commutes with extension. *)

(** 通常输入代入与扩张交换。 *)

Lemma kleisli_extend_pre {X Y Z : @Ob C}
    (f : Hom Y (M Z)) (g : Hom X Y)
  : kleisli_extend (f ∘ g) ≈ kleisli_extend f ∘ fmap M g.
Proof. unfold kleisli_extend. rewrite functor_comp. symmetry. apply comp_assoc. Qed.

(** Ordinary output mapping commutes with extension. *)

(** 通常输出映射与扩张交换。 *)

Lemma kleisli_extend_post {X Y Z : @Ob C}
    (f : Hom Y Z) (g : Hom X (M Y))
  : fmap M f ∘ kleisli_extend g ≈ kleisli_extend (fmap M f ∘ g).
Proof.
  unfold kleisli_extend. rewrite functor_comp, <- !comp_assoc,
    (nt_naturality (μ[M]) f). reflexivity.
Qed.

(** Nested extension is associative; no commutation of effects is used. *)

(** 嵌套扩张满足结合律，不交换效应次序。 *)

Lemma kleisli_extend_assoc {X Y Z : @Ob C}
    (f : Hom X (M Y)) (g : Hom Y (M Z))
  : kleisli_extend (kleisli_extend g ∘ f) ≈
      kleisli_extend g ∘ kleisli_extend f.
Proof.
  unfold kleisli_extend.
  rewrite (@functor_comp C C M _ _ _ (μ[M] Z ∘ fmap M g) f),
    (@functor_comp C C M _ _ _ (μ[M] Z) (fmap M g)), <- !comp_assoc,
    <- (monad_assoc_component M Z).
  rewrite (comp_assoc (μ[M] Z) (μ[M] (M Z))),
    (nt_naturality (μ[M]) g), <- comp_assoc. reflexivity.
Qed.

End Extension.
