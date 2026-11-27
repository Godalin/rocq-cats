From Cats Require Export
  Cat.Computational.Arrow.Pairing
  Cat.Monoidal.Functor.
From Cats Require Import
  Cat.Cartesian.Core
  Cat.Monoidal.Cartesian
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Terminal
  Instance.Set.Product.

Local Open Scope computation_scope.
Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Global Computations as a Lax Monoidal Functor

    Fix an Arrow from a value category with selected finite products into
    a computation category. Terminal-input computations form setoids; pure
    postcomposition and ordered pairing make them a lax monoidal functor.
    The result is setoid-valued, not generally an endofunctor on values. *)

(** * 全局计算作为 lax 幺半函子

    固定从选定有限积的值范畴进入计算范畴的 Arrow。终输入计算组成广集，纯
    后合成及有序配对使其成为 lax 幺半函子。结果为广集值函子，一般并非值
    范畴上的自函子。 *)

(** Apply the existing covariant Hom functor at the image of the terminal object,
    then precompose with [F]. Computation hom and equality
    sizes remain those of [K], independent of the value category. *)

(** 在终对象的像处使用已有协变 Hom 函子，再与 [F] 预复合。计算 Hom 及相等
    大小保留 [K] 的层级，独立于值范畴。 *)

Definition ArrowGlobalF {C K : Cat}
    `{HT : !HasTerminal C} (F : Fct C K)
  : Fct C SetCat
  := Hom(F 1,-) ∘F F.

(** With finite products and an Arrow, ordered pairing equips the
    terminal-input functor with its lax monoidal structure. *)

(** 给定有限积与 Arrow，有序配对赋予终输入函子 lax 幺半结构。 *)

Section GlobalComputations.
Context {C K : Cat} `{HC : !HasCartesian C}
  (A : @Arrow C K CartHasMonoidal).

(** Ordered fanout is a respectful pairing of terminal-input computations. *)

(** 有序 fanout 给出终输入计算的保相等配对。 *)

Program Definition arrow_global_pair (X Y : C)
  : (ArrowGlobalF A X ×S ArrowGlobalF A Y)
    →r ArrowGlobalF A (X × Y)
  := {|func fg := fst fg &&&[A] snd fg|}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg].
  apply arrow_fanout_proper; assumption.
Qed.

(** Pure result naturality supplies the tensorator. Derived tensor maps
    are compared with the chosen product maps before applying pairing laws. *)

(** 纯结果自然性给出 tensorator；先比较派生张量映射与选定积映射，再应用
    配对定律。 *)

Program Definition ArrowGlobalTensorN
  : (tensorF ∘F (ArrowGlobalF A ×F ArrowGlobalF A))
    ⇒ (ArrowGlobalF A ∘F tensorF)
  := {|nt XY := arrow_global_pair (fst XY) (snd XY)|}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  intros [u v].
  change ((arr[A; f] ∘ u) &&&[A] (arr[A; g] ∘ v)
    ≈ arr[A; f ⊗ g] ∘ (u &&&[A] v)).
  rewrite cartesian_tensor_map. symmetry.
  apply arrow_fanout_post.
Qed.

(** Pure identity is the global unit computation. *)

(** 纯恒等为全局单位计算。 *)

Program Definition arrow_global_unit
  : UnitS →r ArrowGlobalF A 1
  := {|func _ := id[A 1]|}.
Next Obligation. intros x y H. reflexivity. Qed.

(** The terminal-input Hom functor is lax monoidal from values to setoids.
    Unit and associativity diagrams are precisely the general pairing laws;
    no internal representation of the hom-setoids is assumed. *)

(** 终输入 Hom 函子是从值到广集的 lax 幺半函子。单位及结合图恰为一般配对律，
    不假设这些 Hom 广集可在值范畴内部表示。 *)

Program Definition ArrowGlobalLax
  : LaxMonoidalFct C SetCat
  := MakeLaxMonoidalFct (ArrowGlobalF A)
    {|lax_unit := arrow_global_unit
    ; lax_tensorN := ArrowGlobalTensorN
    |}.
Next Obligation.
  intros [u f].
  change (arr[A; (π2 : Hom (1 × X) X)]
    ∘ (id[A 1] &&&[A] f) ≈ f).
  apply arrow_fanout_unit_l.
Qed.
Next Obligation.
  intros [f u].
  change (arr[A; (π1 : Hom (X × 1) X)]
    ∘ (f &&&[A] (id[A 1])) ≈ f).
  apply arrow_fanout_unit_r.
Qed.
Next Obligation.
  intros [[f g] h].
  change (arr[A; product_assoc.1]
      ∘ ((f &&&[A] g) &&&[A] h)
    ≈ f &&&[A] (g &&&[A] h)).
  apply arrow_fanout_assoc.
Qed.

(** * Carrying Global Computations through Ordinary Inputs

    Fix an Arrow over selected finite products. Attach a terminal-input
    computation to an ordinary input, retaining its context. Prove pure
    substitution, ordered pairing and nested-context laws without
    exponentials, Monad structure or effect interchange. *)

(** * 普通输入携带全局计算

    固定选定有限积上的 Arrow，将终输入计算附在普通输入旁，并保留其上下文。
    不要求指数、Monad 结构或效应交换，证明纯替换、有序配对及嵌套上下文律。 *)

(** Run a global computation while carrying an ordinary input unchanged. *)

(** 携带不变的普通输入，同时运行一项全局计算。 *)

Definition arrow_global_context {P : C} (X : C)
    (f : Hom (A 1) (A P))
  : Hom (A X) (A (X × P))
  := second[A; f; X] ∘ arr[A; ⟨id, !⟩].

(** Attaching a global result respects its computation equality. *)

(** 附加全局结果保持其计算相等。 *)

Global Instance arrow_global_context_proper
    {P : C} (X : C)
  : Proper (HomEq ==> HomEq) (@arrow_global_context P X).
Proof.
  intros f g H. unfold arrow_global_context.
  rewrite H. reflexivity.
Qed.

(** Inserting the ordinary terminal right context commutes with every
    computation. *)

(** 插入通常的右侧终上下文与每项计算交换。 *)

Lemma arrow_first_unit_inv {X Y : C}
    (k : Hom (A X) (A Y))
  : first[A; k; 1] ∘ arr[A; ⟨id, !⟩]
    ≈ arr[A; ⟨id, !⟩] ∘ k.
Proof.
  transitivity (arr[A; (⟨id, !⟩ : Hom Y (Y × 1))]
    ∘ (arr[A; (π1 : Hom (Y × 1) Y)] ∘ first[A; k; 1])
    ∘ arr[A; (⟨id, !⟩ : Hom X (X × 1))]).
  - rewrite <- comp_assoc, <- fmap_comp.
    apply comp_proper; [| reflexivity].
    assert (Hu : (⟨id, !⟩ : Hom Y (Y × 1)) ∘ π1 ≈ id)
      by exact (fst (CartUnitorRIso.2 Y).2).
    rewrite Hu, fmap_id, comp_id_l. reflexivity.
  - rewrite arrow_first_projection,
      !comp_assoc, <- fmap_comp,
      product_β1, fmap_id, comp_id_r. reflexivity.
Qed.

(** A prior computation runs once; the global result is then paired with its
    output. *)

(** 先前计算只运行一次，再将全局计算结果与其输出配对。 *)

Lemma arrow_global_context_post {P X Y : C}
    (g : Hom (A 1) (A P)) (k : Hom (A X) (A Y))
  : arrow_global_context Y g ∘ k
    ≈ k &&&[A] (g ∘ arr[A; !]).
Proof.
  pose proof (arrow_split_pre A k g id[X]
    (! : Hom X 1)) as H.
  rewrite arrow_arr_id, comp_id_r in H.
  unfold arrow_global_context, arrow_fanout.
  rewrite <- H. unfold arrow_split.
  rewrite !comp_assoc, <- fmap_comp.
  rewrite product_comp_l, !comp_id_r,
    arrow_first_unit_inv. reflexivity.
Qed.

(** Attaching a global result is ordered fanout with the pure input
    identity. *)

(** 附加全局结果就是与纯输入恒等做有序扇出。 *)

Lemma arrow_global_context_fanout {P : C} (X : C)
    (f : Hom (A 1) (A P))
  : arrow_global_context X f
    ≈ id[A X] &&&[A] (f ∘ arr[A; !]).
Proof.
  pose proof (arrow_global_context_post
    f id[A X]) as H.
  rewrite comp_id_r in H. exact H.
Qed.

(** Attaching an ordered pair agrees with attaching the two global
    computations in sequence. *)

(** 附加有序配对，等于依次附加两项全局计算。 *)

Lemma arrow_global_context_pair {P Q : C} (X : C)
    (f : Hom (A 1) (A P)) (g : Hom (A 1) (A Q))
  : arrow_global_context X (f &&&[A] g)
    ≈ arr[A; product_assoc.1]
      ∘ arrow_global_context (X × P) g
        ∘ arrow_global_context X f.
Proof.
  rewrite comp_assoc, arrow_global_context_post, !arrow_global_context_fanout,
    arrow_fanout_pre, arrow_fanout_assoc. reflexivity.
Qed.

(** Mapping a global result is the pure product map after attachment. *)

(** 映射全局结果，等于附加后作纯积映射。 *)

Lemma arrow_global_context_map {P Q : C} (X : C)
    (f : Hom (A 1) (A P)) (h : Hom P Q)
  : arrow_global_context X (arr[A; h] ∘ f)
    ≈ arr[A; id[X] × h] ∘ arrow_global_context X f.
Proof.
  unfold arrow_global_context.
  rewrite arrow_second_comp,
    arrow_second_arr, comp_assoc.
  reflexivity.
Qed.

(** Pure input substitution commutes with attaching the same global
    computation. *)

(** 纯输入替换与附加同一项全局计算交换。 *)

Lemma arrow_global_context_pre {P X Y : C}
    (f : Hom (A 1) (A P)) (h : Hom X Y)
  : arrow_global_context Y f ∘ arr[A; h]
    ≈ arr[A; h × id[P]] ∘ arrow_global_context X f.
Proof.
  unfold arrow_global_context. rewrite !comp_assoc.
  rewrite <- (comp_assoc arr[A; h × id[P]]
    (second[A; f; X])), arrow_second_natural,
    !comp_assoc.
  apply comp_proper; [reflexivity |].
  rewrite <- !fmap_comp. apply fmap_proper.
  rewrite product_comp_r, product_comp_l, !comp_id_l, comp_id_r, term_comp_l.
  reflexivity.
Qed.

(** Attaching a pure global value is ordinary pairing with that value. *)

(** 附加纯全局值，就是与该值作通常配对。 *)

Lemma arrow_global_context_pure {P : C} (X : C)
    (p : Hom 1 P)
  : arrow_global_context X arr[A; p]
    ≈ arr[A; ⟨id, p ∘ !⟩].
Proof.
  unfold arrow_global_context.
  rewrite arrow_second_arr, <- fmap_comp.
  apply fmap_proper.
  rewrite product_comp_l, comp_id_l. reflexivity.
Qed.

(** Nested ordinary context is the selected reassociation of one larger
    context. *)

(** 嵌套通常上下文，等于对一个较大上下文作选定括号重排。 *)

Lemma arrow_global_context_nested {P : C} (Z X : C)
    (f : Hom (A 1) (A P))
  : second[A; arrow_global_context X f; Z]
    ≈ arr[A; product_assoc.1]
      ∘ arrow_global_context (Z × X) f.
Proof.
  unfold arrow_global_context.
  rewrite arrow_second_comp, arrow_second_arr,
    arrow_second_nested, !comp_assoc.
  apply comp_proper; [reflexivity |].
  apply comp_proper; [reflexivity |].
  rewrite <- fmap_comp. apply fmap_proper.
  unfold product_assoc. cbn [projT1 projT2].
  rewrite cross_η, comp_id_l, !product_comp_r,
    !comp_assoc, !product_β1, !product_β2,
    !comp_id_l, term_comp_l.
  rewrite product_β1, product_pair_η.
  reflexivity.
Qed.

End GlobalComputations.
