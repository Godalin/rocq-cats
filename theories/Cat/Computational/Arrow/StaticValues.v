From Cats Require Export
  Cat.Computational.Arrow.Static.
From Cats Require Import
  Cat.Exponential.Laws.

Import Cats.Cat.Exponential.Core.

Local Open Scope applicative_scope.
Local Open Scope computation_scope.

(** * Values of Static Computations

    Fix an Applicative on a category with selected finite products and
    exponentials. Evaluating an internal function on the terminal argument
    identifies static computations with terminal input and global Applicative
    values. The maps also act in any shared external context. All comparisons
    use the specified hom equality; no well-pointedness is assumed. *)

(** * 静态计算的值

    固定选定有限积与指数上的 Applicative。在终参数处求值，将终对象输入的
    静态计算与全局 Applicative 值对应起来。这两个映射也作用于任意共同的
    外部上下文。所有比较使用指定 Hom 相等，不假设良点性。 *)

Section Values.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : Applicative C HT HP).

(** Evaluate the effectful internal function at the terminal argument. *)

(** 在终参数处求值带效应内部函数。 *)

Definition static_value {W Y : @Ob C} (f : Hom W (A (Y ^ 1)%ob))
  : Hom W (A Y)
  := fmap A (exponential_unit_iso Y).1 ∘ f.

(** Abstract a contextual effectful value as a terminal-input function. *)

(** 将上下文中的带效应值抽象为终输入函数。 *)

Definition static_function {W Y : @Ob C} (v : Hom W (A Y))
  : Hom W (A (Y ^ 1)%ob)
  := fmap A (exponential_unit_iso Y).2.1 ∘ v.

(** Evaluation respects the specified equality, including in external contexts. *)

(** 求值保持指定相等，也适用于外部上下文。 *)

Global Instance static_value_proper {W Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@static_value W Y).
Proof. intros f g H. unfold static_value. rewrite H. reflexivity. Qed.

(** Abstraction respects the same equality without comparing function records. *)

(** 抽象保持同一相等，不比较函数记录。 *)

Global Instance static_function_proper {W Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@static_function W Y).
Proof. intros f g H. unfold static_function. rewrite H. reflexivity. Qed.

(** Evaluating the abstraction recovers the value. *)

(** 抽象后求值恢复原值。 *)

Lemma static_value_function {W Y : @Ob C} (v : Hom W (A Y))
  : static_value (static_function v) ≈ v.
Proof.
  unfold static_value, static_function. rewrite <- comp_assoc,
    <- functor_comp, (snd (exponential_unit_iso Y).2.2), functor_id,
    comp_id_l. reflexivity.
Qed.

(** Abstracting the evaluation recovers the internal function. *)

(** 求值后抽象恢复原内部函数。 *)

Lemma static_function_value {W Y : @Ob C} (f : Hom W (A (Y ^ 1)%ob))
  : static_function (static_value f) ≈ f.
Proof.
  unfold static_value, static_function. rewrite <- comp_assoc,
    <- functor_comp, (fst (exponential_unit_iso Y).2.2), functor_id,
    comp_id_l. reflexivity.
Qed.

(** Evaluation commutes with substitution of the external context. *)

(** 求值与外部上下文替换交换。 *)

Lemma static_value_sub {W V Y : @Ob C}
    (f : Hom W (A (Y ^ 1)%ob)) (σ : Hom V W)
  : static_value (f ∘ σ) ≈ static_value f ∘ σ.
Proof. unfold static_value. symmetry. apply comp_assoc. Qed.

(** Abstraction also commutes with substitution of the external context. *)

(** 抽象也与外部上下文替换交换。 *)

Lemma static_function_sub {W V Y : @Ob C}
    (v : Hom W (A Y)) (σ : Hom V W)
  : static_function (v ∘ σ) ≈ static_function v ∘ σ.
Proof. unfold static_function. symmetry. apply comp_assoc. Qed.

(** A pure terminal-input computation evaluates to the ordinary pure value. *)

(** 纯终输入计算求值得到通常纯值。 *)

Lemma static_value_pure {Y : @Ob C} (y : Hom 1 Y)
  : static_value (static_arr A y) ≈ pure[A; y].
Proof.
  unfold static_value, static_arr, applicative_pure_value.
  rewrite <- comp_assoc, <- applicative_pure_natural, comp_assoc.
  apply comp_proper; [reflexivity |].
  apply exponential_unit_name.
Qed.

(** Pure postcomposition recovers the Applicative result map. *)

(** 纯后合成恢复 Applicative 的结果映射。 *)

Lemma static_value_map {Y Z : @Ob C} (g : Hom Y Z)
    (f : Hom 1 (A (Y ^ 1)%ob))
  : static_value (static_arr A g ∘ˢ[A] f) ≈ fmap A g ∘ static_value f.
Proof.
  rewrite static_comp_pure_l. unfold static_value.
  rewrite <- !comp_assoc, <- !functor_comp.
  apply comp_proper; [| reflexivity]. apply functor_fmap_proper.
  exact (exponential_unit_natural g).
Qed.

(** Sequential composition recovers binary Applicative application with the
    value computation before the internal-function computation. No effect
    interchange or monadic dependence is used. *)

(** 顺序复合恢复 Applicative 的二元应用，先执行值计算，再执行内部函数计算。
    不使用效应交换或 Monad 依赖。 *)

Lemma static_value_comp {Y Z : @Ob C}
    (g : Hom 1 (A (Z ^ Y)%ob)) (f : Hom 1 (A (Y ^ 1)%ob))
  : static_value (g ∘ˢ[A] f) ≈
      lift₂[A; app π2 π1; static_value f; g].
Proof.
  unfold static_value, static_comp.
  rewrite applicative_combine_post.
  transitivity (lift₂[A; (app π2 π1) ∘
    (exponential_unit_eval Y × id); f; g]).
  - apply applicative_combine_proper;
      [apply exponential_unit_then | reflexivity | reflexivity].
  - rewrite <- applicative_combine_pre, functor_id, comp_id_l. reflexivity.
Qed.

(** Equality of evaluated values reflects equality of the static functions. *)

(** 求值后值相等，反映原静态函数相等。 *)

Lemma static_value_reflects {W Y : @Ob C}
    (f g : Hom W (A (Y ^ 1)%ob))
    (H : static_value f ≈ static_value g)
  : f ≈ g.
Proof.
  rewrite <- (static_function_value f), <- (static_function_value g).
  rewrite H. reflexivity.
Qed.

(** The inverse comparison sends pure values back to pure static arrows. *)

(** 逆比较将纯值送回纯静态箭头。 *)

Lemma static_function_pure {Y : @Ob C} (y : Hom 1 Y)
  : static_function (pure[A; y]) ≈ static_arr A y.
Proof.
  apply static_value_reflects.
  rewrite static_value_function, static_value_pure. reflexivity.
Qed.

(** Reflect the result-map comparison through the inverse, without equality
    of functor records or their laws. *)

(** 通过逆映射反映结果映射的比较，不要求函子记录或其定律相等。 *)

Lemma static_function_map {Y Z : @Ob C} (g : Hom Y Z)
    (v : Hom 1 (A Y))
  : static_function (fmap A g ∘ v) ≈
      static_arr A g ∘ˢ[A] static_function v.
Proof.
  apply static_value_reflects.
  rewrite static_value_function, static_value_map, static_value_function.
  reflexivity.
Qed.

(** Reflect ordered application as static composition, retaining the same
    effect order on both sides. *)

(** 将有序应用反映为静态复合，两边保持同一效应次序。 *)

Lemma static_function_comp {Y Z : @Ob C}
    (g : Hom 1 (A (Z ^ Y)%ob)) (v : Hom 1 (A Y))
  : static_function (lift₂[A; app π2 π1; v; g]) ≈
      g ∘ˢ[A] static_function v.
Proof.
  apply static_value_reflects.
  rewrite static_value_function, static_value_comp, static_value_function.
  reflexivity.
Qed.

(** Every binary Applicative lifting is represented by static composition:
    first abstract the left value; then produce the right value's partially
    applied ordinary function. The left computation's effects remain first. *)

(** 每个二元 Applicative 提升均可由静态复合表示：先抽象左值，再产生由右值
    部分应用得到的通常函数。左计算的效应仍先执行。 *)

Lemma static_value_binary {X Y Z : @Ob C} (h : Hom (X × Y) Z)
    (u : Hom 1 (A X)) (v : Hom 1 (A Y))
  : static_value ((fmap A (ƛ (h ∘ ⟨π2, π1⟩)) ∘ v) ∘ˢ[A]
      static_function u) ≈ lift₂[A; h; u; v].
Proof.
  rewrite static_value_comp, static_value_function.
  transitivity (lift₂[A; app π2 π1; fmap A id ∘ u;
    fmap A (ƛ (h ∘ ⟨π2, π1⟩)) ∘ v]).
  - rewrite functor_id, comp_id_l. reflexivity.
  - rewrite applicative_combine_pre, exponential_binary_apply. reflexivity.
Qed.

(** The inverse comparison recovers that same sequential representation. *)

(** 逆比较恢复同一个顺序表示。 *)

Lemma static_function_binary {X Y Z : @Ob C} (h : Hom (X × Y) Z)
    (u : Hom 1 (A X)) (v : Hom 1 (A Y))
  : static_function (lift₂[A; h; u; v]) ≈
      (fmap A (ƛ (h ∘ ⟨π2, π1⟩)) ∘ v) ∘ˢ[A] static_function u.
Proof.
  apply static_value_reflects.
  rewrite static_value_function, static_value_binary. reflexivity.
Qed.

End Values.
