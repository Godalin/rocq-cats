From Cats Require Export
  Cat.Core.

(** * Equations through Isomorphisms *)

(** * 通过同构处理等式 *)

Section IsomorphismEquations.
Context {C : Cat}.

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
