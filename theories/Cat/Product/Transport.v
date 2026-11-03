From Cats Require Export Cat.Product.Core.
From Cats Require Import Cat.Core.

(** * Transport of Product Cones *)

(** * 积锥的运输 *)

(** Replacing both projections by equal arrows preserves the full universal
    property and its computational mediator. *)

(** 将两个投影换为指定相等的箭头时，完整泛性质及其可计算中介得到保持。 *)

Definition product_cone_equiv {C : Cat} {X Y P : @Ob C}
    {p p' : Hom P X} {q q' : Hom P Y} (Hp : p ≈ p') (Hq : q ≈ q')
    (HP : is_product X Y P p q)
  : is_product X Y P p' q'.
Proof.
  intros Z f g. destruct (HP Z f g) as [h [Hh Hu]]. exists h.
  refine {|this := _
         ; that := _
         |}.
  - split; [rewrite <- Hp; exact (fst Hh) | rewrite <- Hq; exact (snd Hh)].
  - intros k [H1 H2]. apply Hu. split;
      [rewrite Hp | rewrite Hq]; assumption.
Defined.

(** Isomorphisms in both factors induce an isomorphism of products. *)

(** 两个因子的同构诱导积的同构。 *)

Definition product_iso {C : Cat} `{HP : !HasProduct C}
    {X Y X' Y' : @Ob C} (i : X ≅ X') (j : Y ≅ Y')
  : (X × Y) ≅ (X' × Y').
Proof.
  exists (i.1 × j.1)%hom, (i.2.1 × j.2.1)%hom. split;
    unfold is_linv_of, is_rinv_of;
    rewrite <- cross_comp;
    [rewrite (fst i.2.2), (fst j.2.2) |
     rewrite (snd i.2.2), (snd j.2.2)]; apply cross_id.
Defined.

(** Arrows into any candidate product are determined by both projections. *)

(** 指向任意候选积的箭头由两个投影共同确定。 *)

Lemma product_cone_ext {C : Cat} {X Y P Z : @Ob C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
    {f g : Hom Z P} (H1 : p ∘ f ≈ p ∘ g) (H2 : q ∘ f ≈ q ∘ g)
  : f ≈ g.
Proof.
  transitivity (HP Z (p ∘ g) (q ∘ g)).1.
  - apply (HP Z (p ∘ g) (q ∘ g)).2. split; assumption.
  - symmetry. apply (HP Z (p ∘ g) (q ∘ g)).2. split; reflexivity.
Qed.
