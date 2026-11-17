From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor.

Import Cats.Cat.Exponential.Core.

(** * Evaluation into a Double Exponential

    Fix named products and relative exponentials in an arbitrary category.
    Evaluation defines the ordinary double-dual unit at any result object.
    Its application and naturality laws use specified hom equality. *)

(** * 进入双重指数的求值

    在任意范畴中固定具名积及相对指数。求值在任意结果对象处定义通常双对偶
    单位，其应用与自然性定律使用指定 Hom 相等。 *)

Section DoubleDualEvaluation.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Send a value to evaluation at that value, without a terminal object
    or a classifier assumption. *)

(** 将值送到在该值处的求值，不要求终对象或分类子。 *)

Definition ExpDoubleDualUnit (R X : C)
  : Hom X (R ^ (R ^ X))
  := ƛ (app π2 π1).

(** Application computes evaluation in an arbitrary shared context. *)

(** 应用在任意共同上下文中计算求值。 *)

Theorem exp_double_dual_app {R X Q : C}
    (a : Hom Q X) (p : Hom Q (R ^ X))
  : app (ExpDoubleDualUnit R X ∘ a) p ≈ app p a.
Proof.
  unfold ExpDoubleDualUnit.
  rewrite <- exp_curry_comp_r, exp_app_β,
    !exp_app_comp.
  rewrite ?comp_assoc, ?cross_η, ?product_comp_r, ?comp_assoc,
    ?product_β1, ?product_β2, ?comp_id_l, ?comp_id_r.
  reflexivity.
Qed.

(** Double contravariance makes evaluation natural in the supplied
    arrow, using the existing exponential bifunctor. *)

(** 双重反变使求值对给定箭头自然，复用既有指数双函子。 *)

Theorem exp_double_dual_natural {R X Y : C} (f : Hom X Y)
  : exp_dimap (exp_dimap f (@Cats.Cat.Core.id C R))
      (@Cats.Cat.Core.id C R) ∘ ExpDoubleDualUnit R X
    ≈ ExpDoubleDualUnit R Y ∘ f.
Proof.
  apply exp_ext. rewrite !exp_uncurry_app, !comp_assoc.
  rewrite exp_app_dimap, comp_id_l, exp_double_dual_app,
    exp_app_dimap, comp_id_l, exp_double_dual_app.
  reflexivity.
Qed.

End DoubleDualEvaluation.
