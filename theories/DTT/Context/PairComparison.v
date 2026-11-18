From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Context.Extension
  DTT.Context.Elements
  DTT.Display.Section.

(** * Comparing Substitutions Equipped with Terms

    Keep the original context extensions. The accepted term comparisons
    act on substitution-term pairs without changing their base maps.
    Conversion coherence gives respectfulness; substitution coherence
    gives compatibility with reindexing. No terminal context is used. *)

(** * 比较带项的替换

    固定原上下文扩张，已有项比较作用于替换—项配对而不改变基底映射。
    转换相干性给出保相等性，替换相干性给出重索引相容性；不使用终上下文。 *)

Section ContextElementsPairs.
Context {C : Cat} (T : Fct (C^op) FamCat)
  `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextElements_HasDisplay C T HC.
Let R := @DisplayTyTmF C P HD.

(** Map the term coordinate forward, keeping the supplied substitution. *)

(** 前向映射项坐标，保留给定替换。 *)

Program Definition context_elements_pair_resp {Γ : @Ob C}
    (A : Ty T Γ) (Δ : @Ob C)
  : ContextPairS T A Δ →r ContextPairS R A Δ
  :=
  {|func x := (x.1; context_elements_term_resp T _ x.2)|}.
Next Obligation.
  intros [σ t] [τ u] [H Ht]. exists H.
  transitivity (ty_sub_equiv T H A ▸[R]
    context_elements_term_resp T A[σ]Ty[T] t).
  - apply tm_conv_witness_independent.
  - transitivity (context_elements_term_resp T A[τ]Ty[T]
      (ty_sub_equiv T H A ▸[T] t)).
    + symmetry. exact (@context_elements_term_conv C T HC Δ
        A[σ]Ty[T] A[τ]Ty[T] (ty_sub_equiv T H A) t).
    + exact (@func_proper _ _ (context_elements_term_resp T A[τ]Ty[T])
        _ _ Ht).
Defined.

(** Map the term coordinate backward with the same base substitution. *)

(** 逆向映射项坐标，保留同一基底替换。 *)

Program Definition context_elements_pair_inv_resp {Γ : @Ob C}
    (A : Ty T Γ) (Δ : @Ob C)
  : ContextPairS R A Δ →r ContextPairS T A Δ
  :=
  {|func x := (x.1; context_elements_term_inv_resp T _ x.2)|}.
Next Obligation.
  intros [σ t] [τ u] [H Ht]. exists H.
  transitivity (ty_sub_equiv R H A ▸[T]
    context_elements_term_inv_resp T A[σ]Ty[T] t).
  - apply tm_conv_witness_independent.
  - transitivity (context_elements_term_inv_resp T A[τ]Ty[T]
      (ty_sub_equiv R H A ▸[R] t)).
    + symmetry. exact (@context_elements_term_inv_conv C T HC Δ
        A[σ]Ty[T] A[τ]Ty[T] (ty_sub_equiv R H A) t).
    + exact (@func_proper _ _ (context_elements_term_inv_resp T A[τ]Ty[T])
        _ _ Ht).
Defined.

(** The backward-forward composite preserves substitution-term data. *)

(** 先前向再逆向的复合保留替换—项数据。 *)

Theorem context_elements_pair_β {Γ Δ : @Ob C} (A : Ty T Γ)
    (x : ContextPairS T A Δ)
  : context_elements_pair_inv_resp A Δ
      (context_elements_pair_resp A Δ x) ≈S x.
Proof.
  destruct x as [σ t]. exists (reflS (x := σ)).
  transitivity (context_elements_term_inv_resp T A[σ]Ty[T]
    (context_elements_term_resp T A[σ]Ty[T] t)).
  - apply tm_conv_id.
  - exact (@context_elements_term_β C T HC Δ A[σ]Ty[T] t).
Defined.

(** The forward-backward composite preserves arbitrary recovered pairs. *)

(** 先逆向再前向的复合保留任意恢复配对。 *)

Theorem context_elements_pair_η {Γ Δ : @Ob C} (A : Ty T Γ)
    (x : ContextPairS R A Δ)
  : context_elements_pair_resp A Δ
      (context_elements_pair_inv_resp A Δ x) ≈S x.
Proof.
  destruct x as [σ t]. exists (reflS (x := σ)).
  transitivity (context_elements_term_resp T A[σ]Ty[T]
    (context_elements_term_inv_resp T A[σ]Ty[T] t)).
  - apply tm_conv_id.
  - exact (@context_elements_term_η C T HC Δ A[σ]Ty[T] t).
Defined.

(** The forward map commutes with reindexing, including its composition
    conversion. The term need not be in the image of substitution. *)

(** 前向映射与重索引及其复合转换交换；项不必位于替换的像中。 *)

Theorem context_elements_pair_sub {Γ Δ Θ : @Ob C} (A : Ty T Γ)
    (τ : Hom Θ Δ) (x : ContextPairS T A Δ)
  : context_elements_pair_resp A Θ x[τ]Pair[T, A] ≈S
      (context_elements_pair_resp A Δ x)[τ]Pair[R, A].
Proof.
  destruct x as [σ t]. exists (reflS (x := σ ∘ τ)).
  transitivity (context_elements_term_resp T A[σ ∘ τ]Ty[T]
    (ty_sub_comp T σ τ A ▸[T] t[τ]Tm[T])).
  - apply tm_conv_id.
  - transitivity (ty_sub_comp R σ τ A ▸[R]
      context_elements_term_resp T A[σ]Ty[T][τ]Ty[T] t[τ]Tm[T]).
    + transitivity (ty_sub_comp T σ τ A ▸[R]
        context_elements_term_resp T A[σ]Ty[T][τ]Ty[T] t[τ]Tm[T]).
      * exact (@context_elements_term_conv C T HC Θ _ _
          (ty_sub_comp T σ τ A) t[τ]Tm[T]).
      * apply tm_conv_witness_independent.
    + apply func_proper.
      exact (@context_elements_term_sub C T HC Δ Θ τ A[σ]Ty[T] t).
Defined.

(** The backward map commutes with reindexing of every recovered pair. *)

(** 逆向映射与任意恢复配对的重索引交换。 *)

Theorem context_elements_pair_inv_sub {Γ Δ Θ : @Ob C} (A : Ty T Γ)
    (τ : Hom Θ Δ) (x : ContextPairS R A Δ)
  : context_elements_pair_inv_resp A Θ x[τ]Pair[R, A] ≈S
      (context_elements_pair_inv_resp A Δ x)[τ]Pair[T, A].
Proof.
  destruct x as [σ t]. exists (reflS (x := σ ∘ τ)).
  transitivity (context_elements_term_inv_resp T A[σ ∘ τ]Ty[T]
    (ty_sub_comp R σ τ A ▸[R] t[τ]Tm[R])).
  - apply tm_conv_id.
  - transitivity (ty_sub_comp T σ τ A ▸[T]
      context_elements_term_inv_resp T A[σ]Ty[T][τ]Ty[T] t[τ]Tm[R]).
    + transitivity (ty_sub_comp R σ τ A ▸[T]
        context_elements_term_inv_resp T A[σ]Ty[T][τ]Ty[T] t[τ]Tm[R]).
      * exact (@context_elements_term_inv_conv C T HC Θ _ _
          (ty_sub_comp R σ τ A) t[τ]Tm[R]).
      * apply tm_conv_witness_independent.
    + apply func_proper.
      exact (@context_elements_term_inv_sub C T HC Δ Θ τ A[σ]Ty[T] t).
Defined.

End ContextElementsPairs.
