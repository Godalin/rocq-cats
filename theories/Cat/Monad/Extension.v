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

(** Return an ordinary contextual value. The explicit arrow endpoints
    also keep rewriting independent of identity-functor packaging. *)

(** 返回通常上下文值；显式态射端点也使重写不依赖恒等函子的包装。 *)

Definition monad_return {W X : @Ob C} (x : Hom W X)
  : Hom W (M X)
  := η[M] X ∘ x.

(** Return respects contextual-value equality. *)

(** 返回保持上下文值相等。 *)

Global Instance monad_return_proper {W X : @Ob C}
  : Proper (HomEq ==> HomEq) (@monad_return W X).
Proof. intros x y H. unfold monad_return. rewrite H. reflexivity. Qed.

(** Return commutes with ordinary context substitution. *)

(** 返回与通常上下文代入交换。 *)

Lemma monad_return_comp {W V X : @Ob C} (x : Hom W X) (σ : Hom V W)
  : monad_return x ∘ σ ≈ monad_return (x ∘ σ).
Proof. unfold monad_return. apply comp_assoc. Qed.

(** Mapping a returned value keeps it returned. *)

(** 映射返回值，保持其返回形式。 *)

Lemma monad_return_map {W X Y : @Ob C} (f : Hom X Y) (x : Hom W X)
  : fmap M f ∘ monad_return x ≈ monad_return (f ∘ x).
Proof.
  unfold monad_return.
  rewrite <- comp_assoc, <- (nt_naturality (η[M]) f), comp_assoc.
  reflexivity.
Qed.

(** Return on identity recovers the unit component. *)

(** 返回恒等箭头，恢复单位分量。 *)

Lemma monad_return_id (X : @Ob C)
  : monad_return (@id X) ≈ η[M] X.
Proof. unfold monad_return. apply comp_id_r. Qed.

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

Notation "'return[' M ';' x ']'" := (monad_return M x) : monad_scope.
