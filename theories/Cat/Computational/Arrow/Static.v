From Cats Require Export
  Cat.Computational.Arrow.Global
  Cat.CCC.Core
  Cat.Applicative.Lifting
  Cat.Exponential.Context
  Cat.Exponential.Laws
  Instance.Set.Isomorphism.
From Cats Require Import
  Cat.Product.Transport
  Cat.Monoidal.Cartesian.
Import Cats.Cat.Exponential.Core.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.
Local Open Scope applicative_scope.
Local Open Scope computation_scope.

(** * Static Computations from an Applicative

    A computation is a global effectful internal function. Its effects are
    selected independently of its eventual value input. Composition combines
    the first computation's effects before the second's, then composes the
    resulting functions. Chosen finite products and exponentials suffice;
    no strength, monad or commutativity is assumed. *)

(** * 从 Applicative 得到静态计算

    计算是全局带效应内部函数，其效应的选择独立于最终的值输入。复合先组合
    第一个计算的效应，再组合第二个的效应，最后复合所得函数。选定有限积与
    指数已足够，不假设强度、Monad 或交换性。 *)

Section StaticOperations.
Context {C : Cat}
  `{CC : !HasCC C} (A : Applicative C).

(** Pure lifting names the ordinary arrow before applying the pure map. *)

(** 纯提升先命名通常态射，再作用纯值映射。 *)

Definition static_arr {X Y : C} (f : Hom X Y)
  : Hom 1 (A (Y ^ X))
  := pure[A; exp_name f].

(** Sequential lifting keeps the right-hand computation's effects first. *)

(** 顺序提升让右侧计算的效应先执行。 *)

Definition static_comp {X Y Z : C}
    (g : Hom 1 (A (Z ^ Y))) (f : Hom 1 (A (Y ^ X)))
  : Hom 1 (A (Z ^ X))
  := lift₂[A; internal_then X Y Z; f; g].

End StaticOperations.

Notation "g '∘ˢ[' A ']' f"
  := (static_comp A g f)
  (at level 40, left associativity,
    format "g  ∘ˢ[ A ]  f")
  : computation_scope.

(** ** The Static Computation Category and Arrow

    Fix an Applicative and the selected finite products and exponentials of
    its base. Prove sequential composition laws, then construct the static Arrow. *)

(** ** 静态计算范畴与 Arrow

    固定 Applicative 及其基底的选定有限积与指数，证明顺序复合定律，再构造静态 Arrow。 *)

Section ApplicativeConstruction.
Context {C : Cat}
  `{CC : !HasCC C} (A : Applicative C).

(** Pure lifting respects the specified base equality. *)

(** 纯提升保持指定基底相等。 *)

Global Instance static_arr_proper {X Y : C}
  : Proper (≈[X,Y] ==> HomEq) (static_arr A).
Proof.
  intros f g H. unfold static_arr.
  rewrite H. reflexivity.
Qed.

(** Composition respects both computation equalities. *)

(** 复合保持两个计算相等。 *)

Global Instance static_comp_proper {X Y Z : C}
  : Proper (HomEq ==> HomEq ==> HomEq)
      (@static_comp _ _ A X Y Z).
Proof.
  intros g g' H f f' K. unfold static_comp.
  rewrite H, K. reflexivity.
Qed.

(** A pure first computation substitutes its ordinary input map. *)

(** 纯第一计算代入其通常输入映射。 *)

Lemma static_comp_pure_r {X Y Z : C}
    (g : Hom 1 (A (Z ^ Y))) (f : Hom X Y)
  : g ∘ˢ[A] static_arr A f
    ≈ fmap A (exp_dimap f id) ∘ g.
Proof.
  exact (applicative_combine_pure_l A
    (internal_then X Y Z)
    (exp_name f) (exp_dimap f id)
    (internal_then_name_l f Z) g).
Qed.

(** A pure second computation maps the ordinary result. *)

(** 纯第二计算映射通常结果。 *)

Lemma static_comp_pure_l {X Y Z : C}
    (g : Hom Y Z) (f : Hom 1 (A (Y ^ X)))
  : static_arr A g ∘ˢ[A] f ≈ fmap A (exp_map g) ∘ f.
Proof.
  exact (applicative_combine_pure_r A
    (internal_then X Y Z)
    (exp_name g) (exp_map g)
    (internal_then_name_r g X) f).
Qed.

(** Pure identity is neutral on the input side. *)

(** 纯恒等在输入侧为中性。 *)

Lemma static_comp_id_r {X Y : C}
    (f : Hom 1 (A (Y ^ X)))
  : f ∘ˢ[A] static_arr A (id[X]) ≈ f.
Proof.
  rewrite static_comp_pure_r,
    exp_dimap_id, fmap_id, comp_id_l.
  reflexivity.
Qed.

(** Pure identity is neutral on the output side. *)

(** 纯恒等在输出侧为中性。 *)

Lemma static_comp_id_l {X Y : C}
    (f : Hom 1 (A (Y ^ X)))
  : static_arr A (id[Y]) ∘ˢ[A] f ≈ f.
Proof.
  rewrite static_comp_pure_l,
    exp_map_id, fmap_id, comp_id_l.
  reflexivity.
Qed.

(** Associativity is the existing lax preservation of the internal diagram. *)

(** 结合律就是已有 lax 提升对内部结合图的保持性。 *)

Lemma static_comp_assoc {W X Y Z : C}
    (h : Hom 1 (A (Z ^ Y))) (g : Hom 1 (A (Y ^ X)))
    (f : Hom 1 (A (X ^ W)))
  : (h ∘ˢ[A] g) ∘ˢ[A] f ≈ h ∘ˢ[A] (g ∘ˢ[A] f).
Proof.
  unfold static_comp. symmetry.
  exact (applicative_combine_assoc A
    (internal_then W X Y) (internal_then W Y Z)
    (internal_then X Y Z) (internal_then W X Z)
    (internal_then_assoc W X Y Z) f g h).
Qed.

(** Pure lifting preserves composition. *)

(** 纯提升保持复合。 *)

Lemma static_arr_comp {X Y Z : C} (g : Hom Y Z) (f : Hom X Y)
  : static_arr A (g ∘ f) ≈ static_arr A g ∘ˢ[A] static_arr A f.
Proof.
  unfold static_comp, static_arr. rewrite applicative_combine_pure,
    internal_then_names. reflexivity.
Qed.

(** The hom-sets are global effectful functions with their original
    Type-valued equality. No native function equality is added. *)

(** Hom 广集是全局带效应函数及其原有 Type 值相等，不增加函数原生相等。 *)

Program Definition StaticCat
  : Cat
  :=
  {|Ob := C
  ; HomSet X Y := HomSet 1 (A (Y ^ X))
  ; id X := static_arr A (id[X])
  ; comp X Y Z g f := g ∘ˢ[A] f
  ; comp_proper X Y Z := @static_comp_proper X Y Z
  |}.
Next Obligation. apply static_comp_id_r. Qed.
Next Obligation. apply static_comp_id_l. Qed.
Next Obligation. apply static_comp_assoc. Qed.

(** Embed ordinary arrows as pure named functions, keeping objects fixed. *)

(** 将通常态射嵌入为纯命名函数，对象保持不变。 *)

Program Definition StaticPureF
  : Fct C StaticCat
  :=
  {|fobj X := X
  ; fmap X Y f := static_arr A f
  ; isFct :=
      {|fmap_proper X Y := @static_arr_proper X Y
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. exact (static_arr_comp f g). Qed.

(** Context extension maps the ordinary internal context function. It
    neither runs another effect nor supplies a functor strength. *)

(** 上下文扩展映射通常内部上下文函数，不运行另一个效应，也不提供函子强度。 *)

Definition static_context {X Y : C} (Z : C)
    (f : Hom 1 (A (Y ^ X)))
  : Hom 1 (A ((Z × Y) ^ (Z × X)))
  := fmap A (internal_context Z X Y) ∘ f.

(** Context extension respects computation equality. *)

(** 上下文扩展保持计算相等。 *)

Global Instance static_context_proper {X Y : C} (Z : C)
  : Proper (HomEq ==> HomEq) (@static_context X Y Z).
Proof.
  intros f g H. unfold static_context.
  rewrite H. reflexivity.
Qed.

(** Pure context extension is the pure ordinary product map. *)

(** 纯上下文扩展就是纯通常积映射。 *)

Lemma static_context_arr {X Y : C} (Z : C) (f : Hom X Y)
  : static_context Z (static_arr A f) ≈ static_arr A (id[Z] × f).
Proof.
  unfold static_context, static_arr, applicative_pure_value.
  rewrite <- comp_assoc, <- applicative_pure_natural, comp_assoc.
  apply comp_proper; [reflexivity | exact (internal_context_name Z f)].
Qed.

(** Context extension preserves the same sequential effect order. *)

(** 上下文扩展保持同一效应执行次序。 *)

Lemma static_context_comp {X Y W : C} (Z : C)
    (g : Hom[StaticCat] Y W) (f : Hom[StaticCat] X Y)
  : static_context Z (g ∘ˢ[A] f)
    ≈ static_context Z g ∘ˢ[A] static_context Z f.
Proof.
  unfold static_context, static_comp.
  rewrite applicative_combine_post, applicative_combine_pre,
    internal_context_then. reflexivity.
Qed.

(** Select the static Arrow explicitly. Coherence comes from the general
    internal context diagrams and the same Applicative functor laws. *)

(** 显式选定静态 Arrow。相干性来自一般内部上下文图及同一 Applicative
    函子定律。 *)

Program Definition StaticArrow
  : Arrow C StaticCat
  := MakeArrow StaticPureF
    {|arrow_context X Y Z f := static_context Z f
    ; arrow_context_proper X Y Z := static_context_proper Z
    ; arrow_context_comp X Y W Z g f := static_context_comp Z g f
    |}.
Next Obligation.
  change (static_context Z (static_arr A f)
    ≈ static_arr A (id[Z] ⊗ f)).
  rewrite cartesian_tensor_map. exact (static_context_arr Z f).
Qed.
Next Obligation.
  change (static_arr A (h ⊗ id[Y]) ∘ˢ[A] static_context Z f
    ≈ static_context W f ∘ˢ[A] static_arr A (h ⊗ id[X])).
  rewrite !cartesian_tensor_map.
  rewrite static_comp_pure_l, static_comp_pure_r.
  unfold static_context. rewrite <- !comp_assoc, <- !fmap_comp.
  apply comp_proper; [| reflexivity]. apply fmap_proper.
  exact (internal_context_natural h X Y).
Qed.
Next Obligation.
  change (static_arr A (π2 : Hom (1 × Y) Y) ∘ˢ[A] static_context 1 f
    ≈ f ∘ˢ[A] static_arr A (π2 : Hom (1 × X) X)).
  rewrite static_comp_pure_l, static_comp_pure_r.
  unfold static_context. rewrite <- comp_assoc, <- fmap_comp.
  apply comp_proper; [| reflexivity]. apply fmap_proper.
  exact (internal_context_unit X Y).
Qed.
Next Obligation.
  change (static_arr A product_assoc.1 ∘ˢ[A] static_context (Z × W) f
    ≈ static_context Z (static_context W f) ∘ˢ[A]
      static_arr A product_assoc.1).
  rewrite static_comp_pure_l, static_comp_pure_r.
  unfold static_context. rewrite <- !comp_assoc, <- !fmap_comp.
  apply comp_proper; [| reflexivity]. apply fmap_proper.
  exact (internal_context_assoc Z W X Y).
Qed.

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

(** Evaluate the effectful internal function at the terminal argument. *)

(** 在终参数处求值带效应内部函数。 *)

Definition static_value {W Y : C} (f : Hom W (A (Y ^ 1)))
  : Hom W (A Y)
  := fmap A (exp_unit_iso Y).1 ∘ f.

(** Abstract a contextual effectful value as a terminal-input function. *)

(** 将上下文中的带效应值抽象为终输入函数。 *)

Definition static_function {W Y : C} (v : Hom W (A Y))
  : Hom W (A (Y ^ 1))
  := fmap A (exp_unit_iso Y).2.1 ∘ v.

(** Evaluation respects the specified equality, including in external contexts. *)

(** 求值保持指定相等，也适用于外部上下文。 *)

Global Instance static_value_proper {W Y : C}
  : Proper (HomEq ==> HomEq) (@static_value W Y).
Proof.
  intros f g H. unfold static_value.
  rewrite H. reflexivity.
Qed.

(** Abstraction respects the same equality without comparing function records. *)

(** 抽象保持同一相等，不比较函数记录。 *)

Global Instance static_function_proper {W Y : C}
  : Proper (HomEq ==> HomEq) (@static_function W Y).
Proof.
  intros f g H. unfold static_function.
  rewrite H. reflexivity.
Qed.

(** Evaluating the abstraction recovers the value. *)

(** 抽象后求值恢复原值。 *)

Lemma static_value_function {W Y : C} (v : Hom W (A Y))
  : static_value (static_function v) ≈ v.
Proof.
  unfold static_value, static_function. rewrite <- comp_assoc,
    <- fmap_comp, (snd (exp_unit_iso Y).2.2), fmap_id,
    comp_id_l. reflexivity.
Qed.

(** Abstracting the evaluation recovers the internal function. *)

(** 求值后抽象恢复原内部函数。 *)

Lemma static_function_value {W Y : C} (f : Hom W (A (Y ^ 1)))
  : static_function (static_value f) ≈ f.
Proof.
  unfold static_value, static_function. rewrite <- comp_assoc,
    <- fmap_comp, (fst (exp_unit_iso Y).2.2), fmap_id,
    comp_id_l. reflexivity.
Qed.

(** Evaluation commutes with substitution of the external context. *)

(** 求值与外部上下文替换交换。 *)

Lemma static_value_sub {W V Y : C}
    (f : Hom W (A (Y ^ 1))) (σ : Hom V W)
  : static_value (f ∘ σ) ≈ static_value f ∘ σ.
Proof. unfold static_value. symmetry. apply comp_assoc. Qed.

(** Abstraction also commutes with substitution of the external context. *)

(** 抽象也与外部上下文替换交换。 *)

Lemma static_function_sub {W V Y : C}
    (v : Hom W (A Y)) (σ : Hom V W)
  : static_function (v ∘ σ) ≈ static_function v ∘ σ.
Proof. unfold static_function. symmetry. apply comp_assoc. Qed.

(** A pure terminal-input computation evaluates to the ordinary pure value. *)

(** 纯终输入计算求值得到通常纯值。 *)

Lemma static_value_pure {Y : C} (y : Hom 1 Y)
  : static_value (static_arr A y) ≈ pure[A; y].
Proof.
  unfold static_value, static_arr, applicative_pure_value.
  rewrite <- comp_assoc, <- applicative_pure_natural, comp_assoc.
  apply comp_proper; [reflexivity |].
  apply exp_unit_name.
Qed.

(** Pure postcomposition recovers the Applicative result map. *)

(** 纯后合成恢复 Applicative 的结果映射。 *)

Lemma static_value_map {Y Z : C} (g : Hom Y Z)
    (f : Hom 1 (A (Y ^ 1)))
  : static_value (static_arr A g ∘ˢ[A] f) ≈ fmap A g ∘ static_value f.
Proof.
  rewrite static_comp_pure_l. unfold static_value.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply comp_proper; [| reflexivity]. apply fmap_proper.
  exact (exp_unit_natural g).
Qed.

(** Sequential composition recovers binary Applicative application with the
    value computation before the internal-function computation. No effect
    interchange or monadic dependence is used. *)

(** 顺序复合恢复 Applicative 的二元应用，先执行值计算，再执行内部函数计算。
    不使用效应交换或 Monad 依赖。 *)

Lemma static_value_comp {Y Z : C}
    (g : Hom 1 (A (Z ^ Y))) (f : Hom 1 (A (Y ^ 1)))
  : static_value (g ∘ˢ[A] f) ≈ lift₂[A; app π2 π1; static_value f; g].
Proof.
  unfold static_value, static_comp.
  rewrite applicative_combine_post.
  transitivity (lift₂[A; (app π2 π1) ∘
    (exp_unit_eval Y × id); f; g]).
  - apply applicative_combine_proper;
      [apply exp_unit_then | reflexivity | reflexivity].
  - rewrite <- applicative_combine_pre, fmap_id, comp_id_l. reflexivity.
Qed.

(** Equality of evaluated values reflects equality of the static functions. *)

(** 求值后值相等，反映原静态函数相等。 *)

Lemma static_value_reflects {W Y : C}
    (f g : Hom W (A (Y ^ 1)))
    (H : static_value f ≈ static_value g)
  : f ≈ g.
Proof.
  rewrite <- (static_function_value f), <- (static_function_value g).
  rewrite H. reflexivity.
Qed.

(** The inverse comparison sends pure values back to pure static arrows. *)

(** 逆比较将纯值送回纯静态箭头。 *)

Lemma static_function_pure {Y : C} (y : Hom 1 Y)
  : static_function (pure[A; y]) ≈ static_arr A y.
Proof.
  apply static_value_reflects.
  rewrite static_value_function, static_value_pure. reflexivity.
Qed.

(** Reflect the result-map comparison through the inverse, without equality
    of functor records or their laws. *)

(** 通过逆映射反映结果映射的比较，不要求函子记录或其定律相等。 *)

Lemma static_function_map {Y Z : C} (g : Hom Y Z)
    (v : Hom 1 (A Y))
  : static_function (fmap A g ∘ v) ≈ static_arr A g ∘ˢ[A] static_function v.
Proof.
  apply static_value_reflects.
  rewrite static_value_function, static_value_map, static_value_function.
  reflexivity.
Qed.

(** Reflect ordered application as static composition, retaining the same
    effect order on both sides. *)

(** 将有序应用反映为静态复合，两边保持同一效应次序。 *)

Lemma static_function_comp {Y Z : C}
    (g : Hom 1 (A (Z ^ Y))) (v : Hom 1 (A Y))
  : static_function (lift₂[A; app π2 π1; v; g]) ≈ g ∘ˢ[A] static_function v.
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

Lemma static_value_binary {X Y Z : C} (h : Hom (X × Y) Z)
    (u : Hom 1 (A X)) (v : Hom 1 (A Y))
  : static_value ((fmap A (ƛ (h ∘ ⟨π2, π1⟩)) ∘ v) ∘ˢ[A] static_function u)
    ≈ lift₂[A; h; u; v].
Proof.
  rewrite static_value_comp, static_value_function.
  transitivity (lift₂[A; app π2 π1; fmap A id ∘ u;
    fmap A (ƛ (h ∘ ⟨π2, π1⟩)) ∘ v]).
  - rewrite fmap_id, comp_id_l. reflexivity.
  - rewrite applicative_combine_pre, exp_binary_apply. reflexivity.
Qed.

(** The inverse comparison recovers that same sequential representation. *)

(** 逆比较恢复同一个顺序表示。 *)

Lemma static_function_binary {X Y Z : C} (h : Hom (X × Y) Z)
    (u : Hom 1 (A X)) (v : Hom 1 (A Y))
  : static_function (lift₂[A; h; u; v])
    ≈ (fmap A (ƛ (h ∘ ⟨π2, π1⟩)) ∘ v) ∘ˢ[A] static_function u.
Proof.
  apply static_value_reflects.
  rewrite static_value_function, static_value_binary. reflexivity.
Qed.

(** * Cartesian Operations of Static Arrows

    Fix an Applicative on selected finite products and exponentials. Compare
    the derived first, ordered split and fanout operations with the lifting
    of ordinary internal-function diagrams, then preserve and reflect binary
    Applicative operations through the terminal-input value comparison. *)

(** * 静态 Arrow 的笛卡尔运算

    固定选定有限积与指数上的 Applicative，比较导出的 first、有序 split 和
    fanout 与通常内部函数图的提升，再通过终输入值比较保持与反映二元
    Applicative 运算。 *)

(** The derived static first operation maps the ordinary right-context
    extension. Its conjugating exchanges are pure, so no effects are reordered. *)

(** 导出的静态 first 映射通常右上下文扩展。共轭的交换为纯态射，不重排效应。 *)

Lemma static_first {X Y : C} (Z : C)
    (f : Hom 1 (A (Y ^ X)))
  : first[StaticArrow; f; Z] ≈ fmap A (internal_context_right Z X Y) ∘ f.
Proof.
  unfold arrow_first.
  change ((static_arr A ⟨π2, π1⟩ ∘ˢ[A] static_context Z f) ∘ˢ[A]
    static_arr A ⟨π2, π1⟩
    ≈ fmap A (internal_context_right Z X Y) ∘ f).
  rewrite static_comp_pure_r, static_comp_pure_l.
  unfold static_context, internal_context_right.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply comp_proper; [| reflexivity]. apply fmap_proper.
  rewrite <- exp_dimap_id_r, <- exp_dimap_comp,
    !comp_id_l. reflexivity.
Qed.

(** Ordered splitting lifts the canonical independent-input pairing of
    internal functions. The first computation remains before the second. *)

(** 有序 split 提升内部函数的规范独立输入配对，第一计算仍先于第二计算。 *)

Lemma static_split {X Y X' Y' : C}
    (f : Hom 1 (A (Y ^ X))) (g : Hom 1 (A (Y' ^ X')))
  : f ***[StaticArrow] g
    ≈ lift₂[A; (exp_product_iso (X × X') Y Y').2.1 ∘
        (exp_dimap π1 id × exp_dimap π2 id); f; g].
Proof.
  unfold arrow_split.
  transitivity (static_context Y g ∘ˢ[A]
    (fmap A (internal_context_right X' X Y) ∘ f)).
  { exact (static_comp_proper _ _ (reflexivity _) _ _ (static_first X' f)). }
  change (static_context Y g ∘ˢ[A]
    (fmap A (internal_context_right X' X Y) ∘ f)
    ≈ lift₂[A; (exp_product_iso (X × X') Y Y').2.1 ∘
        (exp_dimap π1 id × exp_dimap π2 id); f; g]).
  unfold static_comp, static_context. rewrite applicative_combine_pre.
  apply applicative_combine_proper;
    [apply internal_context_split | reflexivity | reflexivity].
Qed.

(** The actual Arrow fanout is the Applicative lifting of the existing
    inverse product-exponential comparison, for every ordinary input object. *)

(** 实际 Arrow fanout 就是已有积指数比较之逆的 Applicative 提升，适用于每个
    通常输入对象。 *)

Lemma static_fanout {X Y Z : C}
    (f : Hom 1 (A (Y ^ X))) (g : Hom 1 (A (Z ^ X)))
  : f &&&[StaticArrow] g ≈ lift₂[A; (exp_product_iso X Y Z).2.1; f; g].
Proof.
  unfold arrow_fanout, arrow_split.
  change ((second[StaticArrow; g; Y] ∘ˢ[A]
    first[StaticArrow; f; X]) ∘ˢ[A] static_arr A ⟨id, id⟩
    ≈ lift₂[A; (exp_product_iso X Y Z).2.1; f; g]).
  rewrite static_comp_pure_r, static_first.
  change (fmap A (exp_dimap ⟨id, id⟩ id) ∘
    (static_context Y g ∘ˢ[A]
      (fmap A (internal_context_right X X Y) ∘ f))
    ≈ lift₂[A; (exp_product_iso X Y Z).2.1; f; g]).
  unfold static_context, static_comp.
  rewrite applicative_combine_pre, applicative_combine_post.
  apply applicative_combine_proper; [| reflexivity | reflexivity].
  rewrite <- comp_assoc. apply internal_context_fanout.
Qed.

(** At terminal input, evaluating fanout gives ordered Applicative pairing. *)

(** 在终输入处求值 fanout，得到有序 Applicative 配对。 *)

Lemma static_value_fanout {Y Z : C}
    (f : Hom 1 (A (Y ^ 1))) (g : Hom 1 (A (Z ^ 1)))
  : static_value (f &&&[StaticArrow] g)
    ≈ lift₂[A; id; static_value f; static_value g].
Proof.
  rewrite static_fanout. unfold static_value.
  rewrite applicative_combine_post, applicative_combine_pre, comp_id_l.
  apply applicative_combine_proper;
    [apply exp_unit_product | reflexivity | reflexivity].
Qed.

(** The inverse value comparison turns Applicative pairing back into the
    same derived fanout, using only the specified hom equality. *)

(** 值比较的逆将 Applicative 配对转回同一个导出 fanout，只使用指定 Hom 相等。 *)

Lemma static_function_fanout {Y Z : C}
    (u : Hom 1 (A Y)) (v : Hom 1 (A Z))
  : static_function (lift₂[A; id; u; v])
    ≈ static_function u &&&[StaticArrow] static_function v.
Proof.
  apply static_value_reflects.
  rewrite static_value_function. symmetry.
  etransitivity;
    [exact (static_value_fanout (static_function u) (static_function v)) |].
  rewrite !static_value_function. reflexivity.
Qed.

(** Pure postcomposition of fanout recovers any ordinary binary operation
    lifted by the Applicative, with the same execution order. *)

(** fanout 的纯后合成恢复 Applicative 对任意通常二元运算的提升，保持执行次序。 *)

Lemma static_value_fanout_map {X Y Z : C} (h : Hom (X × Y) Z)
    (f : Hom 1 (A (X ^ 1))) (g : Hom 1 (A (Y ^ 1)))
  : static_value (static_arr A h ∘ˢ[A] (f &&&[StaticArrow] g))
    ≈ lift₂[A; h; static_value f; static_value g].
Proof.
  rewrite static_value_map. etransitivity.
  - apply comp_proper; [reflexivity | exact (static_value_fanout f g)].
  - rewrite applicative_combine_post, comp_id_r. reflexivity.
Qed.

(** Conversely, every binary lifting is represented by the actual fanout
    followed by pure application of its ordinary binary operation. *)

(** 反过来，每个二元提升均由实际 fanout 及其后的通常二元运算纯应用表示。 *)

Lemma static_function_fanout_map {X Y Z : C} (h : Hom (X × Y) Z)
    (u : Hom 1 (A X)) (v : Hom 1 (A Y))
  : static_function (lift₂[A; h; u; v])
    ≈ static_arr A h ∘ˢ[A]
        (static_function u &&&[StaticArrow] static_function v).
Proof.
  apply static_value_reflects.
  rewrite static_value_function. symmetry.
  etransitivity; [exact (static_value_fanout_map h
    (static_function u) (static_function v)) |].
  rewrite !static_value_function. reflexivity.
Qed.

End ApplicativeConstruction.

(** * Interpreting Global Internal Functions

    Fix a cartesian Arrow whose value category has selected exponentials.
    Run a global internal-function computation alongside its ordinary
    argument, then evaluate purely. The generic context laws prove pure,
    sequential and context preservation with independent category sizes;
    no Applicative endofunctor representation is assumed here. *)

(** * 解释全局内部函数

    固定值范畴具有选定指数的笛卡尔 Arrow，将全局内部函数计算与其通常参数
    一起运行，再作纯求值。一般上下文定律在独立范畴大小下证明纯箭头、顺序及
    上下文保持性；此处不假设 Applicative 自函子表示。 *)

Section StaticRepresentation.
Context {C K : Cat}
  `{CC : !HasCC C}.
(** Use the cartesian projections for both evaluation and the global context laws. *)

(** 求值与全局上下文定律通过同一笛卡尔接口取得终对象和积。 *)

Let hc : HasCartesian C := _.
Local Existing Instances hc HasCartesian_hasTerminal HasCartesian_hasProduct.
Context (A : @Arrow C K CartHasMonoidal).

(** Interpret a global internal function by carrying its argument and
    applying ordinary evaluation. *)

(** 携带参数并作通常求值，从而解释全局内部函数。 *)

Definition arrow_static_eval {X Y : C}
    (f : Hom (A 1) (A (Y ^ X)))
  : Hom (A X) (A Y)
  := arr[A; (app π2 π1 : Hom (X × (Y ^ X)) Y)] ∘
    arrow_global_context A X f.

(** Interpretation respects the specified computation equality. *)

(** 解释保持指定的计算相等。 *)

Global Instance arrow_static_eval_proper {X Y : C}
  : Proper (HomEq ==> HomEq) (@arrow_static_eval X Y).
Proof.
  intros f g H. unfold arrow_static_eval. rewrite H. reflexivity.
Qed.

(** Interpreting a pure named function recovers the original pure arrow. *)

(** 解释纯命名函数，恢复原来的纯箭头。 *)

Lemma arrow_static_eval_pure {X Y : C} (f : Hom X Y)
  : arrow_static_eval arr[A; exp_name f] ≈ arr[A; f].
Proof.
  unfold arrow_static_eval. rewrite arrow_global_context_pure, <- fmap_comp.
  apply fmap_proper.
  rewrite exp_app_comp, product_β1, product_β2.
  rewrite exp_name_app, comp_id_r. reflexivity.
Qed.

(** A pure map selecting internal functions can be fused into ordinary
    evaluation. *)

(** 选取内部函数的纯映射可合并到通常求值中。 *)

Lemma arrow_static_eval_map {P X Y : C} (h : Hom P (Y ^ X))
    (f : Hom (A 1) (A P))
  : arrow_static_eval (arr[A; h] ∘ f)
    ≈ arr[A; (app (h ∘ π2) π1 : Hom (X × P) Y)] ∘
        arrow_global_context A X f.
Proof.
  unfold arrow_static_eval. rewrite arrow_global_context_map, <- comp_assoc,
    <- fmap_comp. apply comp_proper; [| reflexivity].
  apply fmap_proper.
  rewrite exp_app_comp.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** Ordered global internal composition interprets as sequential computation
    composition. *)

(** 有序全局内部复合解释为顺序计算复合。 *)

Lemma arrow_static_eval_comp {X Y Z : C}
    (f : Hom (A 1) (A (Y ^ X)))
    (g : Hom (A 1) (A (Z ^ Y)))
  : arrow_static_eval (arr[A; internal_then X Y Z] ∘ (f &&&[A] g))
    ≈ arrow_static_eval g ∘ arrow_static_eval f.
Proof.
  rewrite arrow_static_eval_map, arrow_global_context_pair.
  unfold arrow_static_eval.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (arrow_global_context A Y g)),
    arrow_global_context_pre.
  rewrite <- !comp_assoc.
  apply comp_proper; [| reflexivity]. apply comp_proper; [| reflexivity].
  rewrite <- !fmap_comp. apply fmap_proper.
  unfold product_assoc. cbn [projT1].
  repeat first [rewrite internal_then_app | rewrite exp_app_comp |
    rewrite cross_η | rewrite product_comp_r | rewrite comp_assoc |
    rewrite product_β1 | rewrite product_β2 | rewrite comp_id_l |
    rewrite comp_id_r]. reflexivity.
Qed.

(** Interpreting internal context extension agrees with the original Arrow
    context action. *)

(** 解释内部上下文扩展，与原 Arrow 的上下文作用一致。 *)

Lemma arrow_static_eval_context {X Y : C} (W : C)
    (f : Hom (A 1) (A (Y ^ X)))
  : arrow_static_eval (arr[A; internal_context W X Y] ∘ f)
    ≈ context[A; W; arrow_static_eval f].
Proof.
  rewrite arrow_static_eval_map. unfold arrow_static_eval.
  change (arr[A; (app (internal_context W X Y ∘ π2) π1 :
    Hom ((W × X) × (Y ^ X)) (W × Y))] ∘
      arrow_global_context A (W × X) f
    ≈ second[A; arr[A; (app π2 π1 : Hom (X × (Y ^ X)) Y)] ∘
    arrow_global_context A X f; W]).
  rewrite arrow_second_comp, arrow_second_arr, arrow_global_context_nested,
    <- !comp_assoc.
  apply comp_proper; [| reflexivity].
  rewrite <- fmap_comp. apply fmap_proper.
  rewrite internal_context_app.
  unfold product_assoc. cbn [projT1].
  repeat first [rewrite internal_then_app | rewrite exp_app_comp |
    rewrite cross_η | rewrite product_comp_r | rewrite comp_assoc |
    rewrite product_β1 | rewrite product_β2 | rewrite comp_id_l |
    rewrite comp_id_r]. reflexivity.
Qed.

(** * Static Global-Function Representations

    Fix a cartesian Arrow with selected exponentials. Its specified global-
    function evaluation map is static when each Hom map has an explicit
    inverse. Keep the two category sizes independent; the following
    reification and unique-representation laws assume this property. *)

(** * 全局函数的静态表示

    固定具有选定指数的笛卡尔 Arrow。当其指定全局函数求值的每个 Hom 映射
    具有显式逆时，称该表示为静态。两个范畴大小保持独立；以下恢复与唯一表示定律
    使用此性质。 *)

(** The actual evaluation operation is a map of the native computation Hom
    setoids. *)

(** 实际求值运算是原生计算 Hom 广集之间的映射。 *)

Program Definition arrow_static_eval_resp (X Y : C)
  : HomSet (A 1) (A (Y ^ X)) →r HomSet (A X) (A Y)
  := {|func := arrow_static_eval|}.

(** Staticness means invertibility of these specific evaluation maps,
    retaining inverse witnesses in Type. It is a property of the supplied
    Arrow and choices. *)

(** 静态性表示这些指定求值映射可逆，在 Type 中保留逆见证；它是所给 Arrow 及选择的性质。 *)

Definition is_static_arrow
  : Type
  := ∀ X Y : C, is_iso (C := SetCat) (arrow_static_eval_resp X Y).

(** Reify computations using the chosen inverse of evaluation. *)

(** 用求值的指定逆恢复计算的表示。 *)

Section Reification.
Context (H : is_static_arrow).

(** Recover the global internal-function computation with the specified
    inverse. *)

(** 用指定逆恢复全局内部函数计算。 *)

Definition arrow_reify {X Y : C} (f : Hom (A X) (A Y))
  : Hom (A 1) (A (Y ^ X))
  := (H X Y).1 f.

(** Recovery respects the original computation equality. *)

(** 恢复保持原计算相等。 *)

Global Instance arrow_reify_proper {X Y : C}
  : Proper (HomEq ==> HomEq) (@arrow_reify X Y).
Proof. apply func_proper. Qed.

(** Recovery after evaluation returns the global representation. *)

(** 求值后恢复返回原全局表示。 *)

Lemma arrow_reify_eval {X Y : C} (f : Hom (A 1) (A (Y ^ X)))
  : arrow_reify (arrow_static_eval f) ≈ f.
Proof. exact (fst (H X Y).2 f). Qed.

(** Evaluation after recovery returns the original computation. *)

(** 恢复后求值返回原计算。 *)

Lemma arrow_eval_reify {X Y : C} (f : Hom (A X) (A Y))
  : arrow_static_eval (arrow_reify f) ≈ f.
Proof. exact (snd (H X Y).2 f). Qed.

(** The inverse has the complete unique-representation property in native
    Hom equality. *)

(** 逆映射在原生 Hom 相等下具有完整的唯一表示性质。 *)

Definition arrow_static_universal {X Y : C} (f : Hom (A X) (A Y))
  : is_unique (R := HomEq)
      (λ g, arrow_static_eval g ≈ f) (arrow_reify f)
  := iso_fiber_universal (arrow_static_eval_resp X Y; H X Y) f.

End Reification.

(** * Unique Representations and Structural Recovery

    Fix the same finite-product and exponential data. Characterize
    staticness by Type-valued unique fibers, then prove that its inverse
    preserves pure names, execution-order composition and ordinary context. *)

(** * 唯一表示与结构恢复

    固定同样的有限积与指数数据，以 Type 值唯一纤维刻画静态性，再证明其逆保持
    纯命名、执行次序复合及通常上下文。 *)

(** Supplied Type-valued unique representations construct the actual
    inverse, without an additional choice axiom. *)

(** 给定 Type 值唯一表示即可构造实际逆，不附加选择公理。 *)

Definition static_arrow_of_universal
    (H : ∀ (X Y : C) (f : Hom (A X) (A Y)),
      ∃ g : Hom (A 1) (A (Y ^ X)),
        is_unique (R := HomEq) (λ g, arrow_static_eval g ≈ f) g)
  : is_static_arrow.
Proof.
  intros X Y. apply is_iso_of_unique_fibers. exact (H X Y).
Defined.

(** Invertible evaluation and Type-valued unique representation are
    equivalent criteria. *)

(** 可逆求值与 Type 值唯一表示是等价条件。 *)

Definition static_arrow_universal_iff
  : is_static_arrow
    ↔ (∀ (X Y : C) (f : Hom (A X) (A Y)),
        ∃ g : Hom (A 1) (A (Y ^ X)),
          is_unique (R := HomEq) (λ g, arrow_static_eval g ≈ f) g).
Proof.
  split.
  - intros H X Y f. exists (arrow_reify H f).
    exact (arrow_static_universal H f).
  - exact static_arrow_of_universal.
Defined.

Context (H : is_static_arrow).

(** Under the criterion, evaluation also reflects the specified equality. *)

(** 在该条件下，求值也反映指定相等。 *)

Lemma arrow_static_eval_reflects {X Y : C}
    (f g : Hom (A 1) (A (Y ^ X)))
    (Hfg : arrow_static_eval f ≈ arrow_static_eval g)
  : f ≈ g.
Proof.
  transitivity (arrow_reify H (arrow_static_eval f));
    [symmetry; apply arrow_reify_eval |].
  transitivity (arrow_reify H (arrow_static_eval g));
    [apply arrow_reify_proper; exact Hfg | apply arrow_reify_eval].
Qed.

(** Recovery of a pure arrow is the pure name of that ordinary arrow. *)

(** 纯箭头的恢复是该通常箭头的纯命名。 *)

Lemma arrow_reify_arr {X Y : C} (f : Hom X Y)
  : arrow_reify H arr[A; f] ≈ arr[A; exp_name f].
Proof.
  apply arrow_static_eval_reflects.
  rewrite arrow_eval_reify, arrow_static_eval_pure. reflexivity.
Qed.

(** Recovery preserves sequential execution through ordered global pairing. *)

(** 恢复通过有序全局配对保持顺序执行。 *)

Lemma arrow_reify_comp {X Y Z : C}
    (f : Hom (A X) (A Y)) (g : Hom (A Y) (A Z))
  : arrow_reify H (g ∘ f)
    ≈ arr[A; internal_then X Y Z] ∘ (arrow_reify H f &&&[A] arrow_reify H g).
Proof.
  apply arrow_static_eval_reflects.
  rewrite arrow_eval_reify, arrow_static_eval_comp, !arrow_eval_reify.
  reflexivity.
Qed.

(** Recovery preserves the same original context action through the internal
    context map. *)

(** 恢复通过内部上下文映射保持同一原上下文作用。 *)

Lemma arrow_reify_context {X Y : C} (Z : C)
    (f : Hom (A X) (A Y))
  : arrow_reify H (context[A; Z; f])
    ≈ arr[A; internal_context Z X Y] ∘ arrow_reify H f.
Proof.
  apply arrow_static_eval_reflects.
  etransitivity; [apply arrow_eval_reify |]. symmetry.
  etransitivity.
  - apply arrow_static_eval_context.
  - rewrite (arrow_eval_reify H f). reflexivity.
Qed.

End StaticRepresentation.

(** * Applicative-Generated Static Arrows Satisfy the Criterion

    Fix any Applicative on selected finite products and exponentials.
    Compare actual global-function interpretation with the existing
    terminal-input value map, and reuse its transparent inverse. No setoid-
    base or well-pointedness assumption is needed here. *)

(** * 由 Applicative 生成的静态 Arrow 满足条件

    固定选定有限积与指数上的任意 Applicative，比较实际全局函数解释与已有
    终输入值映射，并复用其透明逆。此处不要求广集基底或良点性。 *)

Section StaticModel.
Context {C : Cat}
  `{CC : !HasCC C} (B : Applicative C).

(** For the actual static Arrow, interpretation is exactly the existing
    terminal-input value map. Only ordinary exponential diagrams are
    compared. *)

(** 对于实际静态 Arrow，解释恰为已有终输入值映射；只比较通常指数图。 *)

Lemma static_eval_value {X Y : C}
    (f : Hom 1 (B ((Y ^ X) ^ 1)))
  : arrow_static_eval (StaticArrow B) f ≈ static_value B f.
Proof.
  unfold arrow_static_eval, arrow_global_context.
  change (static_arr B (app π2 π1 : Hom (X × (Y ^ X)) Y)
      ∘ˢ[B] (static_context B X f ∘ˢ[B] static_arr B ⟨id, !⟩)
    ≈ static_value B f).
  rewrite static_comp_pure_r, static_comp_pure_l.
  unfold static_context, static_value.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply comp_proper; [| reflexivity]. apply fmap_proper.
  rewrite <- exp_dimap_id_r.
  apply exp_ext. rewrite !exp_uncurry_app.
  unfold exp_unit_iso. cbn [projT1].
  unfold exp_unit_eval.
  repeat first [rewrite exp_app_dimap | rewrite internal_context_app |
    rewrite exp_app_comp | rewrite cross_η |
    rewrite product_comp_r | rewrite comp_assoc | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l | rewrite comp_id_r |
    rewrite term_comp_l]. reflexivity.
Qed.

(** Every Applicative-generated static Arrow has the transparent inverse
    already supplied by [static_function]. *)

(** 每个由 Applicative 生成的静态 Arrow 都具有 [static_function] 已提供的透明逆。 *)

Definition static_arrow_is_static
  : is_static_arrow (StaticArrow B).
Proof.
  intros X Y.
  unshelve notypeclasses refine (({|func := static_function B|}); _).
  - apply static_function_proper.
  - split.
    + intros f.
      change (static_function B (arrow_static_eval (StaticArrow B) f) ≈ f).
      rewrite static_eval_value, static_function_value. reflexivity.
    + intros f.
      change (arrow_static_eval (StaticArrow B) (static_function B f) ≈ f).
      rewrite static_eval_value, static_value_function. reflexivity.
Defined.

End StaticModel.
