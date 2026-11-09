From Cats Require Export
  Cat.Core.

(** * Equations through Isomorphisms *)

(** * 通过同构处理等式 *)

(** An isomorphism lets an equation be solved by composing with its
    inverse. The lemmas here package three common steps: identifying
    inverse choices, cancelling an invertible factor, and moving that
    factor across an equation. All conclusions use the category's specified
    hom equality. They neither identify isomorphic objects by native
    equality nor compare the witnesses of inverse laws. *)

(** 同构允许通过复合其逆来求解等式。本模块整理三类常用步骤：证明逆的选择
    相等、消去可逆因子、将该因子移到等式另一边。所有结论都使用范畴指定的
    Hom 相等，既不以原生相等识别同构对象，也不比较互逆定律的见证。 *)

Section IsomorphismEquations.
Context {C : Cat}.

(** A left inverse and a right inverse of the same arrow are equal.
    In particular, two inverse choices agree without comparing their laws. *)

(** 同一箭头的左逆与右逆相等；特别地，两个逆的选择一致，无需比较定律见证。 *)

Lemma inverse_unique {X Y : @Ob C} (f : Hom X Y) (g h : Hom Y X)
    (Hg : is_linv_of f g) (Hh : is_rinv_of f h)
  : g ≈ h.
Proof.
  unfold is_linv_of, is_rinv_of in *.
  transitivity (g ∘ (f ∘ h)).
  - rewrite Hh, comp_id_r. reflexivity.
  - rewrite <- comp_assoc, Hg, comp_id_l. reflexivity.
Qed.

(** Equal arrows share an inverse without comparing inverse witnesses. *)

(** 相等箭头共用同一个逆，不比较逆的见证。 *)

Definition is_iso_equiv {X Y : @Ob C} {f g : Hom X Y}
    (H : f ≈ g) (Hf : is_iso f)
  : is_iso g.
Proof.
  exists Hf.1. split; unfold is_linv_of, is_rinv_of;
    rewrite <- H; [exact (fst Hf.2) | exact (snd Hf.2)].
Defined.

(** Invertible arrows are closed under composition. *)

(** 可逆箭头在复合下封闭。 *)

Definition is_iso_comp {X Y Z : @Ob C} {f : Hom X Y} {g : Hom Y Z}
    (Hf : is_iso f) (Hg : is_iso g)
  : is_iso (g ∘ f)
  := (iso_trans (f; Hf) (g; Hg)).2.

(** Cancel postcomposition by an isomorphism. *)

(** 消去与同构的后合成。 *)

Lemma iso_cancel_l {X Y Z : @Ob C} (i : X ≅ Y) {f g : Hom Z X}
    (H : i.1 ∘ f ≈ i.1 ∘ g)
  : f ≈ g.
Proof.
  assert (K : i.2.1 ∘ (i.1 ∘ f) ≈ i.2.1 ∘ (i.1 ∘ g)).
  { rewrite H. reflexivity. }
  rewrite <- !comp_assoc, (fst i.2.2), !comp_id_l in K. exact K.
Qed.

(** Cancel precomposition by an isomorphism. *)

(** 消去与同构的预合成。 *)

Lemma iso_cancel_r {X Y Z : @Ob C} (i : X ≅ Y) {f g : Hom Y Z}
    (H : f ∘ i.1 ≈ g ∘ i.1)
  : f ≈ g.
Proof.
  assert (K : (f ∘ i.1) ∘ i.2.1 ≈ (g ∘ i.1) ∘ i.2.1).
  { rewrite H. reflexivity. }
  rewrite !comp_assoc, (snd i.2.2), !comp_id_r in K. exact K.
Qed.

(** Move an isomorphism across an equation on the left. *)

(** 将等式左侧的同构移到另一边。 *)

Lemma iso_move_l {X Y Z : @Ob C} (i : X ≅ Y)
    (f : Hom Z X) (g : Hom Z Y)
  : i.1 ∘ f ≈ g ↔ f ≈ i.2.1 ∘ g.
Proof.
  split; intros H.
  - rewrite <- H, <- comp_assoc, (fst i.2.2), comp_id_l. reflexivity.
  - rewrite H, <- comp_assoc, (snd i.2.2), comp_id_l. reflexivity.
Qed.

(** Move an isomorphism across an equation on the right. *)

(** 将等式右侧的同构移到另一边。 *)

Lemma iso_move_r {X Y Z : @Ob C} (i : X ≅ Y)
    (f : Hom Y Z) (g : Hom X Z)
  : f ∘ i.1 ≈ g ↔ f ≈ g ∘ i.2.1.
Proof.
  split; intros H.
  - rewrite <- H, comp_assoc, (snd i.2.2), comp_id_r. reflexivity.
  - rewrite H, comp_assoc, (fst i.2.2), comp_id_r. reflexivity.
Qed.

End IsomorphismEquations.

(** An isomorphism read in the opposite keeps its two arrows and reverses
    the inverse equations. *)

(** 在反范畴中读取同构，保留两条箭头并反转互逆方程。 *)

Definition iso_op {C : Cat} {X Y : @Ob C} (i : X ≅ Y)
  : Y ≅[C^op] X.
Proof.
  exists i.1, i.2.1. split; [exact (snd i.2.2) | exact (fst i.2.2)].
Defined.

Notation "i '^opI'" := (iso_op i) (at level 35) : cat_scope.

(** Postcomposition by an isomorphism has a unique solution for every
    target arrow. Its mediator is inverse composition. *)

(** 与同构后复合的方程对每条目标箭头均有唯一解，中介为与逆的复合。 *)

Definition iso_postcomp_universal {C : Cat} {X Y Z : @Ob C}
    (i : X ≅ Y) (f : Hom Z Y)
  : is_unique (R := @HomEq C Z X)
      (λ g, i.1 ∘ g ≈ f) (i.2.1 ∘ f).
Proof.
  refine {|this := _
          ; that := _
          |}.
  - apply (snd (iso_move_l i _ f)). reflexivity.
  - intros g H. exact (fst (iso_move_l i g f) H).
Defined.

(** Precomposition has the dual universal solution, obtained from the same
    construction in the opposite category. *)

(** 预复合具有对偶的泛解，由反范畴中的同一构造得到。 *)

Definition iso_precomp_universal {C : Cat} {X Y Z : @Ob C}
    (i : X ≅ Y) (f : Hom X Z)
  : is_unique (R := @HomEq C Y Z)
      (λ g, g ∘ i.1 ≈ f) (f ∘ i.2.1)
  := @iso_postcomp_universal (C^op) Y X Z (i^opI) f.
