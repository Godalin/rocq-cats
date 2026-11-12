From Cats Require Export
  Cat.Computational.Arrow.Cartesian
  Cat.Computational.Arrow.Kleisli
  Cat.Monad.Applicative.

Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * The Ordered Kleisli and Applicative Comparison

    Both presentations use the same chosen strong Monad. Their pure maps
    agree and their binary operations run the left computation first.
    This compares those constructions; it is not a conversion of every
    Arrow into an Applicative. *)

(** * 有序 Kleisli 与 Applicative 比较

    两种呈现使用同一个选定强 Monad，纯映射一致，二元运算均先运行左计算。
    这里只比较这些构造，不是将任意 Arrow 转为 Applicative。 *)

Section Comparison.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (M : StrongMonad C (@CartesianMonoidal C HT HP)).

(** Proofs use the contextual equations; computation is restored below. *)

(** 证明使用上下文方程；下方恢复计算透明性。 *)

Local Opaque context_bind monad_return.

(** The pure-arrow functor uses the original Monad return. *)

(** 纯箭头函子使用原 Monad 返回。 *)

Lemma kleisli_arrow_arr {X Y : @Ob C} (f : Hom X Y)
  : arr[KleisliArrow M; f] ≈ return[M; f].
Proof. reflexivity. Qed.

(** Acting on the second factor binds its computation and returns the
    retained ordinary first factor with the computed value. *)

(** 对第二个因子的作用绑定其计算，再将保留的通常第一因子与计算值一同返回。 *)

Lemma kleisli_arrow_second {X Y : @Ob C} (f : Hom X (M Y)) (Z : @Ob C)
  : second[KleisliArrow M; f; Z] ≈
      bind[M; f ∘ π2; return[M; ⟨π1 ∘ π1, π2⟩]].
Proof.
  change (st[hasStrength M; Z; Y] ∘
    (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _ (@id Z) f) ≈
    bind[M; f ∘ π2; return[M; ⟨π1 ∘ π1, π2⟩]]).
  rewrite cartesian_tensor_map, context_bind_pair, cross_η, comp_id_l.
  reflexivity.
Qed.

(** Acting on the first factor retains the ordinary second factor. *)

(** 对第一个因子的作用保留通常第二因子。 *)

Lemma kleisli_arrow_first {X Y : @Ob C} (f : Hom X (M Y)) (Z : @Ob C)
  : first[KleisliArrow M; f; Z] ≈
      bind[M; f ∘ π1; return[M; ⟨π2, π2 ∘ π1⟩]].
Proof.
  unfold arrow_first. rewrite kleisli_arrow_second.
  change ((return[M; (⟨π2, π1⟩ : Hom (Z × Y) (Y × Z))] ∘K[M]
    bind[M; f ∘ π2; return[M; ⟨π1 ∘ π1, π2⟩]]) ∘K[M]
      return[M; (⟨π2, π1⟩ : Hom (X × Z) (Z × X))] ≈
      bind[M; f ∘ π1; return[M; ⟨π2, π2 ∘ π1⟩]]).
  rewrite kleisli_comp_pure_l, kleisli_comp_pure_r.
  monad_context_simpl M. reflexivity.
Qed.

(** Ordered splitting is precisely the already constructed Monad pairing
    after the two ordinary input computations. *)

(** 有序分开组合恰为已有 Monad 配对，在两个通常输入计算之后作用。 *)

Lemma kleisli_arrow_split {X Y X' Y' : @Ob C}
    (f : Hom X (M Y)) (g : Hom X' (M Y'))
  : (f ***[KleisliArrow M] g) ≈ monad_pair M ∘ (f × g).
Proof.
  unfold arrow_split. rewrite kleisli_arrow_first, kleisli_arrow_second.
  change (kleisli_extend M
    (bind[M; g ∘ π2; return[M; ⟨π1 ∘ π1, π2⟩]]) ∘
      bind[M; f ∘ π1; return[M; ⟨π2, π2 ∘ π1⟩]] ≈
      monad_pair M ∘ (f × g)).
  rewrite <- context_bind_discard, monad_pair_pre.
  monad_context_simpl M. reflexivity.
Qed.

(** Fanout and Applicative pairing agree in every shared ordinary context. *)

(** 在任意共同通常上下文中，扇出与 Applicative 配对一致。 *)

Lemma kleisli_arrow_fanout {W X Y : @Ob C}
    (f : Hom W (M X)) (g : Hom W (M Y))
  : (f &&&[KleisliArrow M] g) ≈ monad_pair M ∘ ⟨f, g⟩.
Proof.
  unfold arrow_fanout.
  change ((f ***[KleisliArrow M] g) ∘K[M] return[M; ⟨id, id⟩] ≈
    monad_pair M ∘ ⟨f, g⟩).
  rewrite kleisli_comp_pure_r, kleisli_arrow_split, comp_assoc.
  apply comp_proper; [reflexivity |].
  pose proof (@product_comp_l C HP W W (M X) (M Y) W id id f g) as H.
  rewrite !comp_id_r in H. exact H.
Qed.

(** Specializing splitting to two computation-valued inputs recovers the
    tensorator of the existing lawful Applicative. *)

(** 将分开组合特化到两个计算值输入，恢复已有带定律 Applicative 的 tensorator。 *)

Lemma kleisli_arrow_applicative_pair (X Y : @Ob C)
  : (@id (M X)) ***[KleisliArrow M] (@id (M Y)) ≈
      φ₂[MonadA M; X; Y].
Proof.
  rewrite kleisli_arrow_split, cross_id, comp_id_r. reflexivity.
Qed.

Local Transparent context_bind monad_return.

End Comparison.
