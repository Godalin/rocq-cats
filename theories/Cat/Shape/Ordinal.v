From Cats.Set Require Export Ordinal.
From Cats Require Export Cat.Preorder.
From Cats Require Import Instance.Nat.Order.
From Cats Require Import
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

(** * Finite Ordinals

    [n] has n+1 objects, numbered 0 through n, and one arrow i → j for i ≤
    j. *)

(** * 有限序数

    [n] 对应从零到 n 的 n+1 个对象；当 i ≤ j 时存在唯一箭头 i → j。 *)

(** ** Reading from Shapes to Simplicial Sets

    A point, an edge and a filled triangle suggest dimensions zero, one and
    two. To describe their faces without measuring lengths or angles, number
    their vertices in order. The symbol [n] stands for the ordered list from
    zero to n: its dimension is n, but it has n+1 positions. In particular,
    [Ord 0] has one object, not none.

    Here an ordered list is made into a category: there is one arrow from
    i to j when i is at most j. A functor between these categories is a
    monotone map of positions. It may skip or identify positions, but cannot
    reverse their order. %\coqref{Cats.Cat.Shape.Ordinal.OrdinalShape}
    {%[OrdinalShape]%}% packages this elementary model;
    the later %\coqref{Cats.Cat.Shape.Simplex.Core.SimplexCat}
    {%[SimplexCat]%}% collects all its sizes.

    On a first reading, follow these questions rather than every helper proof:
    - Shapes: what are the ordered vertices, faces and repeated positions?
    - Simplicial sets: what data does a shape select, and how are faces read?
    - Standard simplices and nerves: what do those data look like in examples?
    - Extensions: can partial boundary data be filled, or maps joined by a
      homotopy?

    The chapter order follows this path while placing every formal dependency
    before its use. Universe lifts and transport proofs support the interfaces;
    the low-dimensional examples explain what those interfaces represent. *)

(** ** 从形状读到单纯集合

    点、边和填满的三角形分别提示零、一、二维。为了描述它们的面而不测量长度
    或角度，先给顶点按顺序编号。[n] 表示从零到 n 的有序列表：维数是 n，
    位置却有 n+1 个。特别地，[Ord 0] 有一个对象，并非没有对象。

    此处把有序列表变成范畴：i 不大于 j 时，从 i 到 j 恰有一条箭头。
    这些范畴之间的函子就是位置的保序映射，可以跳过位置，也可以合并位置，
    但不能颠倒顺序。%\coqref{Cats.Cat.Shape.Ordinal.OrdinalShape}
    {%[OrdinalShape]%}% 包装这个初等模型；后面的
    %\coqref{Cats.Cat.Shape.Simplex.Core.SimplexCat}
    {%[SimplexCat]%}% 再把各个大小汇集起来。

    初读时可以先沿下面的问题前进，再回头细读辅助证明：
    - 形状：有序顶点、面和重复位置分别是什么？
    - 单纯集合：一个形状对应什么数据，怎样取出它的面？
    - 标准单形与 nerve：在具体例子里，这些数据长什么样？
    - 进一步的问题：部分边界能否填充，映射之间能否用同伦连接？

    章节按这条路线安排，同时保证形式依赖先于使用者出现。宇宙提升与运输证明
    支撑接口，低维例子则解释接口所表示的数学内容。 *)

Definition OrdinalShape (n : nat)
  : Cat
  := @PreorderCat (Ordinal n) (λ i j, NatLe (fin_rank i) (fin_rank j))
    (pullback_preorder NatLe fin_rank).

Notation "'[Ord' n ']'" := (OrdinalShape n) : cat_scope.

(** The unique arrow from the least finite ordinal position. *)

(** 从有限序数最小位置出发的唯一箭头。 *)

Definition ordinal_from_first {n : nat} (i : Ordinal n)
  : (@Hom (OrdinalShape n)) fin_first i
  := tt.

(** The least ordinal position is initial; its universal arrows are the
    already specified arrows from the first position. *)

(** 序数的最小位置是始对象，其泛箭头沿用从首位置出发的既有箭头。 *)

Definition ordinal_first_initial (n : nat)
  : @is_initial [Ord n] fin_first.
Proof.
  intros i. exists (ordinal_from_first i).
  refine {|this := I
          ; that := _
          |}.
  intros f H. exact tt.
Defined.

(** Construct a finite-ordinal functor from a rank-monotone map. Arithmetic
    inequalities are converted back to computational Type-valued arrows. *)

(** 从编号保序映射构造有限序数函子，将算术不等式恢复为可计算的 Type 值箭头。 *)

Definition OrdinalF {n m : nat} (f : Ordinal n → Ordinal m)
    (Hf : ∀ x y, fin_rank x ≤ fin_rank y → fin_rank (f x) ≤ fin_rank (f y))
  : Functor [Ord n] [Ord m]
  := PreorderF
      (HR := pullback_preorder NatLe fin_rank)
      (HS := pullback_preorder NatLe fin_rank)
      f (λ x y H, nat_le_of_le (Hf x y (nat_le_to_le H))).

(** Every finite-ordinal functor preserves the arithmetic order of ranks. *)

(** 每个有限序数函子都保持编号的算术顺序。 *)

Definition ordinal_functor_monotone {n m : nat}
    (F : Functor [Ord n] [Ord m]) (x y : Ordinal n)
    (H : fin_rank x ≤ fin_rank y)
  : fin_rank (F x) ≤ fin_rank (F y).
Proof.
  apply (@nat_le_to_le (fin_rank (F x)) (fin_rank (F y))).
  exact (fmap F (X := x) (Y := y)
    (@nat_le_of_le (fin_rank x) (fin_rank y) H)).
Defined.

(** Isomorphic positions in a finite ordinal have the same rank and hence
    are equal as finite positions. No general object-equality principle is
    used; this is a fact about this concrete order. *)

(** 有限序数中同构的位置编号相同，故作为有限位置相等。这是具体顺序的性质，
    不使用一般的对象相等原则。 *)

Lemma ordinal_iso_eq {n : nat} {x y : Ordinal n}
    (e : x ≅[OrdinalShape n] y)
  : x = y.
Proof.
  apply fin_rank_injective.
  pose proof (@nat_le_to_le (fin_rank x) (fin_rank y) e.1).
  pose proof (@nat_le_to_le (fin_rank y) (fin_rank x) e.2.1). lia.
Qed.

(** Equal object ranks give the unique pointwise order arrows of a natural
    comparison. The comparison remains computational in its numeric ranks. *)

(** 对象编号相等给出唯一的逐点顺序箭头，组成自然比较；比较在数字编号上保持
    可计算。 *)

Program Definition OrdinalCompareN {n m : nat}
    (F G : Functor [Ord n] [Ord m])
    (H : ∀ x, fin_rank (F x) = fin_rank (G x))
  : F ⇒ G
  :=
  {|nt x := @nat_le_of_le (fin_rank (F x)) (fin_rank (G x)) _
  |}.
Next Obligation. rewrite H. reflexivity. Defined.
Next Obligation. exact tt. Defined.

(** Equality of ranks supplies an invertible natural comparison. *)

(** 编号相等提供可逆的自然比较。 *)

Definition ordinal_functor_rank_iso {n m : nat}
    (F G : Functor [Ord n] [Ord m])
    (H : ∀ x, fin_rank (F x) = fin_rank (G x))
  : F ≅N G.
Proof.
  exists (OrdinalCompareN F G H). intros x.
  exists (OrdinalCompareN G F (λ y, eq_sym (H y)) x).
  split; exact tt.
Defined.

(** For these finite orders, natural isomorphism is exactly pointwise
    equality on positions, without equality of functor records. *)

(** 对于这些有限顺序，自然同构恰为位置上的逐点相等，不等同函子记录。 *)

Definition ordinal_functor_iso_iff {n m : nat}
    (F G : Functor [Ord n] [Ord m])
  : F ≅N G ↔ ∀ x, F x = G x.
Proof.
  split.
  - intros [α Hα] x. exact (ordinal_iso_eq (α x; Hα x)).
  - intros H. apply ordinal_functor_rank_iso. intros x. now rewrite H.
Defined.

(** Rebuilding a functor from its monotone object map loses no information
    up to natural isomorphism. No arrow-map or law-field equality is needed. *)

(** 从保序对象映射重建函子，在自然同构下不丢失信息；不比较箭头映射或定律
    字段的原生相等。 *)

Definition ordinal_functor_rebuild_iso {n m : nat}
    (F : Functor [Ord n] [Ord m])
  : OrdinalF F (ordinal_functor_monotone F) ≅N F.
Proof. apply ordinal_functor_rank_iso. intros x. reflexivity. Defined.

(** The arrow between consecutive positions of a finite ordinal. *)

(** 有限序数中相邻位置之间的箭头。 *)

Definition ordinal_step {n : nat} (i : Fin@{Set} n)
  : (@Hom [Ord n]) (fin_weaken i) (fin_next i).
Proof.
  apply nat_le_of_le. rewrite fin_weaken_rank. cbn. lia.
Defined.

(** Naturality on consecutive arrows implies naturality on every interval.
    This is the generating-arrow principle for ordinal diagrams, valid in
    any category with its specified hom equality. *)

(** 相邻箭头上的自然性蕴涵每个区间上的自然性。这是序数图式的生成箭头原理，
    对任意带指定 Hom 相等的范畴成立。 *)

Lemma ordinal_naturality_steps {C : Cat} {n : nat}
    (F G : Functor [Ord n] C) (α : ∀ i, Hom (F i) (G i))
    (H : ∀ i : Fin@{Set} n,
      α (fin_next i) ∘ fmap F (ordinal_step i) ≈
        fmap G (ordinal_step i) ∘ α (fin_weaken i))
  : ∀ i j (f : (@Hom [Ord n]) i j),
      α j ∘ fmap F f ≈ fmap G f ∘ α i.
Proof.
  assert (Hid : ∀ {m} (P Q : Functor [Ord m] C)
      (β : ∀ i, Hom (P i) (Q i)) i (f : (@Hom [Ord m]) i i),
      β i ∘ fmap P f ≈ fmap Q f ∘ β i).
  { intros m P Q β i f.
    rewrite (@functor_fmap_proper _ _ P i i f
      (@Cats.Cat.Core.id [Ord m] i) tt),
      (@functor_fmap_proper _ _ Q i i f
      (@Cats.Cat.Core.id [Ord m] i) tt),
      !functor_id, comp_id_l, comp_id_r. reflexivity. }
  induction n as [|n IH] in F, G, α, H |- *.
  - intros [[] | []] [[] | []] f. apply Hid.
  - assert (Hnext : ∀ i j : Ordinal n,
        fin_rank i ≤ fin_rank j →
          fin_rank (fin_next i) ≤ fin_rank (fin_next j)).
    { cbn. intros. lia. }
    pose (Q := OrdinalF (@fin_next (S n)) Hnext).
    assert (Htail : ∀ i j (f : (@Hom [Ord n]) i j),
      α (fin_next j) ∘ fmap F (fmap Q f) ≈
        fmap G (fmap Q f) ∘ α (fin_next i)).
    { apply (IH (F ∘F Q) (G ∘F Q)). intros i.
      change (α (fin_next (fin_next i)) ∘
        fmap F (fmap Q (ordinal_step i)) ≈
        fmap G (fmap Q (ordinal_step i)) ∘
          α (fin_next (fin_weaken i))).
      rewrite (@functor_fmap_proper _ _ F _ _
        (fmap Q (ordinal_step i)) (ordinal_step (fin_next i)) tt),
        (@functor_fmap_proper _ _ G _ _
        (fmap Q (ordinal_step i)) (ordinal_step (fin_next i)) tt).
      exact (H (fin_next i)). }
    intros [[] | i] [[] | j] f.
    + apply Hid.
    + pose (a := ordinal_step (@fin_first n)).
      pose (b := fmap Q (ordinal_from_first j)).
      transitivity (α (fin_next j) ∘ (fmap F b ∘ fmap F a)).
      * apply comp_proper; [reflexivity |].
        transitivity (fmap F (b ∘ a)).
        -- apply functor_fmap_proper. exact tt.
        -- exact (@functor_comp _ _ F _ _ _ b a).
      * transitivity ((α (fin_next j) ∘ fmap F b) ∘ fmap F a).
        { symmetry. apply comp_assoc. }
        transitivity ((fmap G b ∘ α (fin_next fin_first)) ∘ fmap F a).
        { apply comp_proper; [exact (Htail fin_first j _) | reflexivity]. }
        transitivity (fmap G b ∘ (α (fin_next fin_first) ∘ fmap F a)).
        { apply comp_assoc. }
        transitivity (fmap G b ∘ (fmap G a ∘ α fin_first)).
        { apply comp_proper; [reflexivity | exact (H fin_first)]. }
        transitivity ((fmap G b ∘ fmap G a) ∘ α fin_first).
        { symmetry. apply comp_assoc. }
        apply comp_proper; [|reflexivity]. symmetry.
        transitivity (fmap G (b ∘ a)).
        -- apply functor_fmap_proper. exact tt.
        -- exact (@functor_comp _ _ G _ _ _ b a).
    + destruct f.
    + rewrite (@functor_fmap_proper _ _ F _ _ f (fmap Q f) tt),
        (@functor_fmap_proper _ _ G _ _ f (fmap Q f) tt).
      exact (Htail i j f).
Defined.
