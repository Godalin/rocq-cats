From Cats Require Export
  Cat.Monad.Kleisli
  Cat.Monad.Adjunction.
From Cats Require Import
  Cat.Adjunction.

Local Open Scope monad_scope.

(** * The Kleisli Comparison of an Adjunction

    Fix an ordinary adjunction with independently sized categories. Its
    induced Monad has a canonical Kleisli comparison into the adjunction's
    target: keep the left adjoint on objects and inverse-transpose arrows.
    The comparison is fully faithful with explicit transpose preimages.
    No strength, products or object representatives are needed. *)

(** * 伴随的 Kleisli 比较

    固定两个大小独立的范畴之间的普通伴随。诱导 Monad 的 Kleisli 范畴具有到
    伴随目标范畴的规范比较：对象沿左伴随映射，箭头作逆转置。比较全忠实，
    原像显式取转置，不需要强度、积或对象代表。 *)

Section Comparison.
Context {C D : Cat} {F : Fct C D} {U : Fct D C} (A : F ⊣ U).

(** Inverse transposition turns Kleisli composition into target composition.
    Multiplication is the image of the counit; reuse inverse naturality. *)

(** 逆转置将 Kleisli 复合变为目标复合。乘法为余单位的像，证明复用逆转置自然性。 *)

Lemma adjunction_kleisli_unadjunct_comp {X Y Z : @Ob C}
    (f : Hom Y (U (F Z))) (g : Hom X (U (F Y)))
  : (f ∘K[AdjMonad A] g)^♭[A] ≈ f^♭[A] ∘ g^♭[A].
Proof.
  change ((fmap U (adj_counit A (F Z)) ∘
    fmap U (fmap F f) ∘ g)^♭[A] ≈ f^♭[A] ∘ g^♭[A]).
  rewrite <- functor_comp, <- (unadjunct_counit A f).
  apply unadjunct_comp_l.
Qed.

(** The comparison functor uses the left adjoint on objects and the supplied
    inverse Hom correspondence on arrows. *)

(** 比较函子在对象上使用左伴随，在箭头上使用所给 Hom 逆对应。 *)

Program Definition AdjKleisliF
  : Fct (KleisliCat (AdjMonad A)) D
  :=
  {|F0 := F
  ; F1 X Y f := f^♭[A]
  ; functor_fmap_proper X Y := unadjunct_proper A
  |}.
Next Obligation. exact (adjunction_β A (@id (F X))). Defined.

Next Obligation. exact (adjunction_kleisli_unadjunct_comp f g). Defined.

(** Transposition supplies computational fullness witnesses and reflects
    equality through the two inverse laws. The target need not consist only
    of image objects, so essential surjectivity is not asserted. *)

(** 转置提供可计算满性见证，并由两条互逆律反映相等。目标不必只有像对象，
    因此这里不宣称本质满。 *)

Definition adjunction_kleisli_fully_faithful
  : is_fully_faithful AdjKleisliF.
Proof.
  split.
  - intros X Y f. exists (f^♯[A]). exact (adjunction_β A f).
  - intros X Y f g E.
    transitivity ((f^♭[A])^♯[A]); [symmetry; exact (adjunction_η A f)|].
    transitivity ((g^♭[A])^♯[A]).
    + exact (@adjunct_proper C D F U A X (F Y) _ _ E).
    + exact (adjunction_η A g).
Defined.

End Comparison.
