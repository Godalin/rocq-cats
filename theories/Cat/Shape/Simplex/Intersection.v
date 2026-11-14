From Cats Require Export
  Cat.Shape.Simplex.Operators.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Intersections of Two Faces

    Two distinct faces of an (n+2)-simplex meet in an n-face. The local
    index inside one face is the preimage of the position omitted by the
    other. These indices compute with finite ordinals. The factorization
    below retains an actual common shape map, including when its source
    has higher degree and contains degeneracies. *)

(** * 两个面的交叠

    一个 (n+2)-单形的两个不同面相交于一个 n-面。在一面内的局部索引，是
    另一面所省略位置的原像。这些索引由有限序数计算。下述分解保留实际的
    共同形状映射，即使其源维度更高并包含退化。 *)

(** The position in face j omitted by face k. *)

(** 面 k 在面 j 内省略的位置。 *)

Definition coface_intersection_index {n : nat}
    (j k : Ordinal (S (S n))) (H : ¬ j = k)
  : Ordinal (S n)
  := (@fin_unskip (S (S n)) j k (λ E, H (symmetry E))).1.

(** The local index recovers the other omitted position. *)

(** 局部索引恢复另一面省略的位置。 *)

Lemma coface_intersection_index_β {n : nat}
    (j k : Ordinal (S (S n))) (H : ¬ j = k)
  : δ[S n; j] (coface_intersection_index j k H) = k.
Proof. exact (@fin_unskip (S (S n)) j k _).2. Defined.

(** Both routes select precisely the positions other than j and k. *)

(** 两条路径都恰好选取 j、k 以外的位置。 *)

Lemma coface_intersection_swap {n : nat}
    (j k : Ordinal (S (S n))) (H : ¬ j = k)
  : δ[S n; j] ∘ δ[n; coface_intersection_index j k H] ≈
      δ[S n; k] ∘
        δ[n; coface_intersection_index k j (λ E, H (symmetry E))].
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  change (@fin_skip (S (S n)) j
    (@fin_skip (S n) (coface_intersection_index j k H) z) =
    @fin_skip (S (S n)) k (@fin_skip (S n)
      (coface_intersection_index k j (λ E, H (symmetry E))) z)).
  apply fin_skip_exchange.
  - exact (coface_intersection_index_β j k H).
  - exact (coface_intersection_index_β k j (λ E, H (symmetry E))).
Defined.

(** Every common factor passes through the intersection cofaces. Its
    mediator is computed by [CofacePreimageF]; equality stays in Δ. *)

(** 每个共同因子都经过交叠余面分解；中介由 [CofacePreimageF] 计算，相等仍
    使用 Δ 的指定相等。 *)

Definition CofaceIntersectionFactor {m n : nat}
    (j k : Ordinal (S (S n))) (H : ¬ j = k)
    (f g : (@Hom Δ) m (S n))
    (E : δ[S n; j] ∘ f ≈ δ[S n; k] ∘ g)
  : ∃ h : (@Hom Δ) m n,
      (δ[n; coface_intersection_index j k H] ∘ h ≈ f) ∧
      (δ[n; coface_intersection_index k j
        (λ F, H (symmetry F))] ∘ h ≈ g).
Proof.
  pose (v := coface_intersection_index j k H).
  assert (Hf : ∀ z, ¬ f z = v).
  { intros z F. apply (@fin_skip_avoids (S (S n)) k (g z)).
    change (δ[S n; k] (g z) = k).
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    change (δ[S n; j] (f z) = δ[S n; k] (g z)) in Ez.
    rewrite <- Ez, F. apply coface_intersection_index_β. }
  exists (CofacePreimageF v f Hf). split.
  - apply coface_preimage_β.
  - apply (snd (simplex_eq_iff _ _)). intros z.
    apply (@fin_skip_injective (S (S n)) k).
    pose proof (fst (simplex_eq_iff _ _)
      (coface_intersection_swap j k H)
      (CofacePreimageF v f Hf z)) as Es.
    pose proof (fst (simplex_eq_iff _ _)
      (coface_preimage_β v f Hf) z) as Ef.
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    change (δ[S n; k]
      (δ[n; coface_intersection_index k j (λ F, H (symmetry F))]
        (CofacePreimageF v f Hf z)) = δ[S n; k] (g z)).
    change (δ[S n; j]
      (δ[n; coface_intersection_index j k H]
        (CofacePreimageF v f Hf z)) = δ[S n; k]
        (δ[n; coface_intersection_index k j (λ F, H (symmetry F))]
          (CofacePreimageF v f Hf z))) in Es.
    change (δ[n; v] (CofacePreimageF v f Hf z) = f z) in Ef.
    change (δ[S n; j] (f z) = δ[S n; k] (g z)) in Ez.
    rewrite <- Es. fold v. rewrite Ef. exact Ez.
Defined.
