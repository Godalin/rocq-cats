From Cats Require Export
  Cat.Computational.Arrow.StaticValues
  Cat.Computational.Arrow.Cartesian.
From Cats Require Import
  Cat.Exponential.Laws.

Local Open Scope applicative_scope.
Local Open Scope computation_scope.

(** * Cartesian Operations of Static Arrows

    Fix an Applicative on selected finite products and exponentials. Compare
    the derived first, ordered split and fanout operations with the lifting
    of ordinary internal-function diagrams, then preserve and reflect binary
    Applicative operations through the terminal-input value comparison. *)

(** * 静态 Arrow 的笛卡尔运算

    固定选定有限积与指数上的 Applicative，比较导出的 first、有序 split 和
    fanout 与通常内部函数图的提升，再通过终输入值比较保持与反映二元
    Applicative 运算。 *)

Section StaticCartesian.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : Applicative C HT HP).

(** The derived static first operation maps the ordinary right-context
    extension. Its conjugating exchanges are pure, so no effects are reordered. *)

(** 导出的静态 first 映射通常右上下文扩展。共轭的交换为纯态射，不重排效应。 *)

Lemma static_first {X Y : @Ob C} (Z : @Ob C)
    (f : Hom 1 (A (Y ^ X)%ob))
  : first[StaticArrow A; f; Z] ≈
      fmap A (internal_context_right Z X Y) ∘ f.
Proof.
  unfold arrow_first.
  change ((static_arr A ⟨π2, π1⟩ ∘ˢ[A] static_context A Z f) ∘ˢ[A]
    static_arr A ⟨π2, π1⟩ ≈
      fmap A (internal_context_right Z X Y) ∘ f).
  rewrite static_comp_pure_r, static_comp_pure_l.
  unfold static_context, internal_context_right.
  rewrite <- !comp_assoc, <- !functor_comp.
  apply comp_proper; [| reflexivity]. apply functor_fmap_proper.
  rewrite <- exponential_dimap_id_r, <- exponential_dimap_comp,
    !comp_id_l. reflexivity.
Qed.

(** Ordered splitting lifts the canonical independent-input pairing of
    internal functions. The first computation remains before the second. *)

(** 有序 split 提升内部函数的规范独立输入配对，第一计算仍先于第二计算。 *)

Lemma static_split {X Y X' Y' : @Ob C}
    (f : Hom 1 (A (Y ^ X)%ob)) (g : Hom 1 (A (Y' ^ X')%ob))
  : f ***[StaticArrow A] g ≈
      lift₂[A; (exponential_product_iso (X × X') Y Y').2.1 ∘
        (exponential_dimap π1 id × exponential_dimap π2 id); f; g].
Proof.
  unfold arrow_split. rewrite static_first.
  change (static_context A Y g ∘ˢ[A]
    (fmap A (internal_context_right X' X Y) ∘ f) ≈
      lift₂[A; (exponential_product_iso (X × X') Y Y').2.1 ∘
        (exponential_dimap π1 id × exponential_dimap π2 id); f; g]).
  unfold static_comp, static_context. rewrite applicative_combine_pre.
  apply applicative_combine_proper;
    [apply internal_context_split | reflexivity | reflexivity].
Qed.

(** The actual Arrow fanout is the Applicative lifting of the existing
    inverse product-exponential comparison, for every ordinary input object. *)

(** 实际 Arrow fanout 就是已有积指数比较之逆的 Applicative 提升，适用于每个
    通常输入对象。 *)

Lemma static_fanout {X Y Z : @Ob C}
    (f : Hom 1 (A (Y ^ X)%ob)) (g : Hom 1 (A (Z ^ X)%ob))
  : f &&&[StaticArrow A] g ≈
      lift₂[A; (exponential_product_iso X Y Z).2.1; f; g].
Proof.
  unfold arrow_fanout, arrow_split.
  change ((second[StaticArrow A; g; Y] ∘ˢ[A]
    first[StaticArrow A; f; X]) ∘ˢ[A] static_arr A ⟨id, id⟩ ≈
      lift₂[A; (exponential_product_iso X Y Z).2.1; f; g]).
  rewrite static_comp_pure_r, static_first.
  change (fmap A (exponential_dimap ⟨id, id⟩ id) ∘
    (static_context A Y g ∘ˢ[A]
      (fmap A (internal_context_right X X Y) ∘ f)) ≈
      lift₂[A; (exponential_product_iso X Y Z).2.1; f; g]).
  unfold static_context, static_comp.
  rewrite applicative_combine_pre, applicative_combine_post.
  apply applicative_combine_proper; [| reflexivity | reflexivity].
  rewrite <- comp_assoc. apply internal_context_fanout.
Qed.

(** At terminal input, evaluating fanout gives ordered Applicative pairing. *)

(** 在终输入处求值 fanout，得到有序 Applicative 配对。 *)

Lemma static_value_fanout {Y Z : @Ob C}
    (f : Hom 1 (A (Y ^ 1)%ob)) (g : Hom 1 (A (Z ^ 1)%ob))
  : static_value A (f &&&[StaticArrow A] g) ≈
      lift₂[A; id; static_value A f; static_value A g].
Proof.
  rewrite static_fanout. unfold static_value.
  rewrite applicative_combine_post, applicative_combine_pre, comp_id_l.
  apply applicative_combine_proper;
    [apply exponential_unit_product | reflexivity | reflexivity].
Qed.

(** The inverse value comparison turns Applicative pairing back into the
    same derived fanout, using only the specified hom equality. *)

(** 值比较的逆将 Applicative 配对转回同一个导出 fanout，只使用指定 Hom 相等。 *)

Lemma static_function_fanout {Y Z : @Ob C}
    (u : Hom 1 (A Y)) (v : Hom 1 (A Z))
  : static_function A (lift₂[A; id; u; v]) ≈
      static_function A u &&&[StaticArrow A] static_function A v.
Proof.
  apply (static_value_reflects A).
  rewrite static_value_function. symmetry.
  etransitivity;
    [exact (static_value_fanout (static_function A u) (static_function A v)) |].
  rewrite !static_value_function. reflexivity.
Qed.

(** Pure postcomposition of fanout recovers any ordinary binary operation
    lifted by the Applicative, with the same execution order. *)

(** fanout 的纯后合成恢复 Applicative 对任意通常二元运算的提升，保持执行次序。 *)

Lemma static_value_fanout_map {X Y Z : @Ob C} (h : Hom (X × Y) Z)
    (f : Hom 1 (A (X ^ 1)%ob)) (g : Hom 1 (A (Y ^ 1)%ob))
  : static_value A (static_arr A h ∘ˢ[A] (f &&&[StaticArrow A] g)) ≈
      lift₂[A; h; static_value A f; static_value A g].
Proof.
  rewrite static_value_map. etransitivity.
  - apply comp_proper; [reflexivity | exact (static_value_fanout f g)].
  - rewrite applicative_combine_post, comp_id_r. reflexivity.
Qed.

(** Conversely, every binary lifting is represented by the actual fanout
    followed by pure application of its ordinary binary operation. *)

(** 反过来，每个二元提升均由实际 fanout 及其后的通常二元运算纯应用表示。 *)

Lemma static_function_fanout_map {X Y Z : @Ob C} (h : Hom (X × Y) Z)
    (u : Hom 1 (A X)) (v : Hom 1 (A Y))
  : static_function A (lift₂[A; h; u; v]) ≈
      static_arr A h ∘ˢ[A]
        (static_function A u &&&[StaticArrow A] static_function A v).
Proof.
  apply (static_value_reflects A).
  rewrite static_value_function. symmetry.
  etransitivity; [exact (static_value_fanout_map h
    (static_function A u) (static_function A v)) |].
  rewrite !static_value_function. reflexivity.
Qed.

End StaticCartesian.
