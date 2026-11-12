From Cats Require Export
  Cat.Computational.Arrow.Core
  Cat.Applicative.Lifting
  Cat.Exponential.Context.
From Cats Require Import
  Cat.Product.Transport
  Cat.Monoidal.Cartesian.

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

(** Pure lifting names the ordinary arrow before applying the pure map. *)

(** 纯提升先命名通常态射，再作用纯值映射。 *)

Definition static_arr {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} {HE : HasExponential HP}
    (A : Applicative C HT HP) {X Y : @Ob C} (f : Hom X Y)
  : Hom 1 (A (Y ^ X)%ob)
  := pure[A; exponential_name f].

(** Sequential lifting keeps the right-hand computation's effects first. *)

(** 顺序提升让右侧计算的效应先执行。 *)

Definition static_comp {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} {HE : HasExponential HP}
    (A : Applicative C HT HP) {X Y Z : @Ob C}
    (g : Hom 1 (A (Z ^ Y)%ob)) (f : Hom 1 (A (Y ^ X)%ob))
  : Hom 1 (A (Z ^ X)%ob)
  := lift₂[A; internal_then X Y Z; f; g].

Notation "g '∘ˢ[' A ']' f" := (static_comp A g f)
  (at level 40, left associativity) : computation_scope.

Section Static.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : Applicative C HT HP).

(** Pure lifting respects the specified base equality. *)

(** 纯提升保持指定基底相等。 *)

Global Instance static_arr_proper {X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@static_arr C HT HP HE A X Y).
Proof. intros f g H. unfold static_arr. rewrite H. reflexivity. Qed.

(** Composition respects both computation equalities. *)

(** 复合保持两个计算相等。 *)

Global Instance static_comp_proper {X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq) (@static_comp C HT HP HE A X Y Z).
Proof. intros g g' H f f' K. unfold static_comp. rewrite H, K. reflexivity. Qed.

(** A pure first computation substitutes its ordinary input map. *)

(** 纯第一计算代入其通常输入映射。 *)

Lemma static_comp_pure_r {X Y Z : @Ob C}
    (g : Hom 1 (A (Z ^ Y)%ob)) (f : Hom X Y)
  : g ∘ˢ[A] static_arr A f ≈ fmap A (exponential_dimap f id) ∘ g.
Proof.
  exact (applicative_combine_pure_l A (internal_then X Y Z)
    (exponential_name f) (exponential_dimap f id)
    (internal_then_name_l f Z) g).
Qed.

(** A pure second computation maps the ordinary result. *)

(** 纯第二计算映射通常结果。 *)

Lemma static_comp_pure_l {X Y Z : @Ob C}
    (g : Hom Y Z) (f : Hom 1 (A (Y ^ X)%ob))
  : static_arr A g ∘ˢ[A] f ≈ fmap A (exponential_map g) ∘ f.
Proof.
  exact (applicative_combine_pure_r A (internal_then X Y Z)
    (exponential_name g) (exponential_map g) (internal_then_name_r g X) f).
Qed.

(** Pure identity is neutral on the input side. *)

(** 纯恒等在输入侧为中性。 *)

Lemma static_comp_id_r {X Y : @Ob C} (f : Hom 1 (A (Y ^ X)%ob))
  : f ∘ˢ[A] static_arr A (@id X) ≈ f.
Proof.
  rewrite static_comp_pure_r, exponential_dimap_id, functor_id, comp_id_l.
  reflexivity.
Qed.

(** Pure identity is neutral on the output side. *)

(** 纯恒等在输出侧为中性。 *)

Lemma static_comp_id_l {X Y : @Ob C} (f : Hom 1 (A (Y ^ X)%ob))
  : static_arr A (@id Y) ∘ˢ[A] f ≈ f.
Proof.
  rewrite static_comp_pure_l, exponential_map_id, functor_id, comp_id_l.
  reflexivity.
Qed.

(** Associativity is the existing lax preservation of the internal diagram. *)

(** 结合律就是已有 lax 提升对内部结合图的保持性。 *)

Lemma static_comp_assoc {W X Y Z : @Ob C}
    (h : Hom 1 (A (Z ^ Y)%ob)) (g : Hom 1 (A (Y ^ X)%ob))
    (f : Hom 1 (A (X ^ W)%ob))
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

Lemma static_arr_comp {X Y Z : @Ob C} (g : Hom Y Z) (f : Hom X Y)
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
  {|Ob := @Ob C
  ; HomSet X Y := @HomSet C 1 (A (Y ^ X)%ob)
  ; id X := static_arr A (@id X)
  ; comp X Y Z g f := g ∘ˢ[A] f
  ; comp_proper X Y Z := @static_comp_proper X Y Z
  |}.
Next Obligation. apply static_comp_id_r. Defined.
Next Obligation. apply static_comp_id_l. Defined.
Next Obligation. apply static_comp_assoc. Defined.

(** Embed ordinary arrows as pure named functions, keeping objects fixed. *)

(** 将通常态射嵌入为纯命名函数，对象保持不变。 *)

Program Definition StaticPureF
  : Functor C StaticCat
  :=
  {|F0 X := X
  ; F1 X Y f := static_arr A f
  ; functor_fmap_proper X Y := @static_arr_proper X Y
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation. exact (static_arr_comp f g). Defined.

(** Context extension maps the ordinary internal context function. It
    neither runs another effect nor supplies a functor strength. *)

(** 上下文扩展映射通常内部上下文函数，不运行另一个效应，也不提供函子强度。 *)

Definition static_context {X Y : @Ob C} (Z : @Ob C)
    (f : Hom 1 (A (Y ^ X)%ob))
  : Hom 1 (A ((Z × Y) ^ (Z × X))%ob)
  := fmap A (internal_context Z X Y) ∘ f.

(** Context extension respects computation equality. *)

(** 上下文扩展保持计算相等。 *)

Global Instance static_context_proper {X Y : @Ob C} (Z : @Ob C)
  : Proper (HomEq ==> HomEq) (@static_context X Y Z).
Proof. intros f g H. unfold static_context. rewrite H. reflexivity. Qed.

(** Pure context extension is the pure ordinary product map. *)

(** 纯上下文扩展就是纯通常积映射。 *)

Lemma static_context_arr {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
  : static_context Z (static_arr A f) ≈ static_arr A (@id Z × f).
Proof.
  unfold static_context, static_arr, applicative_pure_value.
  rewrite <- comp_assoc, <- applicative_pure_natural, comp_assoc.
  apply comp_proper; [reflexivity | exact (internal_context_name Z f)].
Qed.

(** Context extension preserves the same sequential effect order. *)

(** 上下文扩展保持同一效应执行次序。 *)

Lemma static_context_comp {X Y W : @Ob C} (Z : @Ob C)
    (g : (@Hom StaticCat) Y W) (f : (@Hom StaticCat) X Y)
  : static_context Z (g ∘ˢ[A] f) ≈
      static_context Z g ∘ˢ[A] static_context Z f.
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
  : Arrow C StaticCat (@CartesianMonoidal C HT HP)
  :=
  {|ArrowF := StaticPureF
  ; arrow_context X Y Z f := static_context Z f
  ; arrow_context_proper X Y Z := static_context_proper Z
  ; arrow_context_comp X Y W Z g f := static_context_comp Z g f
  |}.
Next Obligation.
  rewrite cartesian_tensor_map. exact (static_context_arr Z f).
Defined.
Next Obligation.
  rewrite !cartesian_tensor_map.
  change (static_arr A (h × @id Y) ∘ˢ[A] static_context Z f ≈
    static_context W f ∘ˢ[A] static_arr A (h × @id X)).
  rewrite static_comp_pure_l, static_comp_pure_r.
  unfold static_context. rewrite <- !comp_assoc, <- !functor_comp.
  apply comp_proper; [| reflexivity]. apply functor_fmap_proper.
  exact (internal_context_natural h X Y).
Defined.
Next Obligation.
  change (static_arr A (π2 : Hom (1 × Y) Y) ∘ˢ[A] static_context 1 f ≈
    f ∘ˢ[A] static_arr A (π2 : Hom (1 × X) X)).
  rewrite static_comp_pure_l, static_comp_pure_r.
  unfold static_context. rewrite <- comp_assoc, <- functor_comp.
  apply comp_proper; [| reflexivity]. apply functor_fmap_proper.
  exact (internal_context_unit X Y).
Defined.
Next Obligation.
  change (static_arr A (@product_assoc C HP Z W Y).1 ∘ˢ[A]
    static_context (Z × W) f ≈
    static_context Z (static_context W f) ∘ˢ[A]
      static_arr A (@product_assoc C HP Z W X).1).
  rewrite static_comp_pure_l, static_comp_pure_r.
  unfold static_context. rewrite <- !comp_assoc, <- !functor_comp.
  apply comp_proper; [| reflexivity]. apply functor_fmap_proper.
  exact (internal_context_assoc Z W X Y).
Defined.

End Static.
