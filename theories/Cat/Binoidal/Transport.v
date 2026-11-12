From Cats Require Export
  Cat.Binoidal.Center.

Local Open Scope binoidal_scope.

(** * Transporting Tensor Boundaries *)

(** * 运输张量边界 *)

Section Transport.
Context {C : Cat} `{BC : !BinoidalCat C}.

(** Each context functor preserves transported identities. *)

(** 每个上下文函子保持运输后的恒等态射。 *)

Lemma binoidal_left_eq_to_hom (Z : @Ob C) {X Y : @Ob C} (p : X = Y)
  : Z ⊲ eq_to_hom p ≈ eq_to_hom (f_equal (λ Q, Z ⊗ Q) p).
Proof. exact (fmap_eq_to_hom (BinoidalLeftF Z) p). Qed.

(** The same statement holds for a context on the right. *)

(** 对右侧上下文有同样的结论。 *)

Lemma binoidal_right_eq_to_hom (Z : @Ob C) {X Y : @Ob C} (p : X = Y)
  : eq_to_hom p ⊳ Z ≈ eq_to_hom (f_equal (λ Q, Q ⊗ Z) p).
Proof. exact (fmap_eq_to_hom (BinoidalRightF Z) p). Qed.

(** Changing the fixed context along an equality is natural in an arbitrary
    computation, by centrality of the transported identity. *)

(** 沿相等改变固定上下文时，对任意计算自然；这来自运输恒等的中心性。 *)

Lemma binoidal_context_eq {Z W : @Ob C} (p : Z = W)
    {X Y : @Ob C} (f : Hom X Y)
  : eq_to_hom (f_equal (λ Q, Q ⊗ Y) p) ∘ (Z ⊲ f) ≈
      (W ⊲ f) ∘ eq_to_hom (f_equal (λ Q, Q ⊗ X) p).
Proof.
  pose proof (fst (eq_to_hom_central p X Y f)) as H.
  rewrite !binoidal_right_eq_to_hom in H. exact H.
Qed.

End Transport.
