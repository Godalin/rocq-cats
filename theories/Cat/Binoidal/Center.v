From Cats Require Export
  Cat.Binoidal.Core.
From Cats Require Import
  Cat.Isomorphism.

Local Open Scope binoidal_scope.

(** * Central Arrows

    A central arrow may exchange execution order with any other arrow
    on either side of the tensor. This is extra evidence for a specified
    arrow, not an interchange law for arbitrary computations. *)

(** * 中心态射

    中心态射可在张量的任意一侧与另一任意态射交换执行次序。这是指定态射的
    额外证据，不是任意计算之间的交换律。 *)

Definition is_central {C : Cat} `{BC : !BinoidalCat C}
    {X Y : @Ob C} (f : Hom X Y)
  := ∀ Z W (g : Hom Z W),
    (f ⊳ W) ∘ (X ⊲ g) ≈ (Y ⊲ g) ∘ (f ⊳ Z) ∧
    (W ⊲ f) ∘ (g ⊳ X) ≈ (g ⊳ Y) ∘ (Z ⊲ f).

Section CentralLaws.
Context {C : Cat} `{BC : !BinoidalCat C}.

(** Centrality is invariant under specified hom equality. *)

(** 中心性在指定 Hom 相等下不变。 *)

Definition central_equiv {X Y : @Ob C} {f g : Hom X Y}
    (H : f ≈ g) (Hf : is_central f)
  : is_central g.
Proof.
  intros Z W h. destruct (Hf Z W h) as [H1 H2]. split;
    rewrite <- H; assumption.
Defined.

(** The same transport gives respectfulness in both directions. *)

(** 同一运输给出双向保相等性。 *)

Global Instance is_central_proper {X Y : @Ob C}
  : Proper (HomEq ==> iffT) (@is_central C BC X Y).
Proof.
  intros f g H. split; intros Hf.
  - exact (central_equiv H Hf).
  - symmetry in H. exact (central_equiv H Hf).
Defined.

(** Identities commute with every computation in either position. *)

(** 恒等态射在两个位置都与任意计算交换。 *)

Definition central_id (X : @Ob C)
  : is_central (@id X).
Proof.
  intros Z W g. split;
    rewrite ?binoidal_left_id, ?binoidal_right_id,
      comp_id_l, comp_id_r; reflexivity.
Defined.

(** Composing central arrows retains both exchange witnesses. *)

(** 复合中心态射保留两种交换见证。 *)

Definition central_comp {X Y U : @Ob C}
    (g : Hom Y U) (f : Hom X Y) (Hg : is_central g) (Hf : is_central f)
  : is_central (g ∘ f).
Proof.
  intros Z W h. destruct (Hg Z W h) as [Hg1 Hg2].
  destruct (Hf Z W h) as [Hf1 Hf2]. split.
  - rewrite !binoidal_right_comp, comp_assoc, Hf1,
      <- comp_assoc, Hg1, comp_assoc. reflexivity.
  - rewrite !binoidal_left_comp, comp_assoc, Hf2,
      <- comp_assoc, Hg2, comp_assoc. reflexivity.
Defined.

(** The inverse of a central isomorphism is central. Each exchange square
    is inverted using functoriality of the corresponding context action. *)

(** 中心同构的逆仍为中心态射。借助相应上下文作用的函子性，分别反转两个
    交换方块。 *)

Definition central_inv {X Y : @Ob C} (i : X ≅ Y)
    (Hi : is_central i.1)
  : is_central i.2.1.
Proof.
  intros Z W g. destruct (Hi Z W g) as [H1 H2]. split.
  - exact (iso_square_inv
      (i.1 ⊳ Z; functor_is_iso (BinoidalRightF Z) i.1 i.2)
      (i.1 ⊳ W; functor_is_iso (BinoidalRightF W) i.1 i.2)
      (X ⊲ g) (Y ⊲ g) H1).
  - exact (iso_square_inv
      (Z ⊲ i.1; functor_is_iso (BinoidalLeftF Z) i.1 i.2)
      (W ⊲ i.1; functor_is_iso (BinoidalLeftF W) i.1 i.2)
      (g ⊳ X) (g ⊳ Y) H2).
Defined.

(** Centrality equates the two execution orders with the central arrow
    in the first tensor position. *)

(** 当中心态射位于张量第一位置时，中心性给出两种执行次序相等。 *)

Lemma central_sequence {X Y Z W : @Ob C}
    (f : Hom X Y) (g : Hom Z W) (Hf : is_central f)
  : binoidal_sequence f g ≈ (f ⊳ W) ∘ (X ⊲ g).
Proof. symmetry. exact (fst (Hf Z W g)). Qed.

(** Centrality of the other factor also suffices to exchange the order. *)

(** 另一因子的中心性也足以交换执行次序。 *)

Lemma central_sequence_r {X Y Z W : @Ob C}
    (f : Hom X Y) (g : Hom Z W) (Hg : is_central g)
  : binoidal_sequence f g ≈ (f ⊳ W) ∘ (X ⊲ g).
Proof. exact (snd (Hg X Y f)). Qed.

End CentralLaws.

(** Ordered tensoring preserves composition when the later left arrow
    exchanges with the earlier right arrow. No other centrality is needed. *)

(** 后执行的左态射可与先执行的右态射交换时，有序张量保持复合；不需其他
    中心性条件。 *)

Lemma central_sequence_comp {C : Cat} `{BC : !BinoidalCat C}
    {X X' X'' Y Y' Y'' : @Ob C}
    (f' : Hom X' X'') (f : Hom X X')
    (g' : Hom Y' Y'') (g : Hom Y Y') (Hf' : is_central f')
  : binoidal_sequence (f' ∘ f) (g' ∘ g) ≈
      binoidal_sequence f' g' ∘ binoidal_sequence f g.
Proof.
  unfold binoidal_sequence.
  rewrite binoidal_left_comp, binoidal_right_comp, !comp_assoc.
  rewrite <- (comp_assoc (X'' ⊲ g) (f' ⊳ Y) (f ⊳ Y)),
    <- (fst (Hf' Y Y' g)), comp_assoc. reflexivity.
Qed.
