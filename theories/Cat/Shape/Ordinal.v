From Cats.Set Require Export Ordinal.
From Cats Require Export Cat.Preorder.
From Cats Require Import Instance.Nat.Order.
From Cats Require Import
  Cat.Functor.Core
  Cat.Natural.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

(** * Finite Ordinals

    [n] has n+1 objects, numbered 0 through n, and one arrow i → j for i ≤
    j. *)

(** * 有限序数

    [n] 对应从零到 n 的 n+1 个对象；当 i ≤ j 时存在唯一箭头 i → j。 *)

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
