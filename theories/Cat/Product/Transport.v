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

(** Transport a product along an apex isomorphism commuting with its legs. *)

(** 沿与锥腿交换的顶点同构运输积。 *)

Definition product_apex_iso {C : Cat} {X Y P Q : @Ob C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
    (i : P ≅ Q) (p' : Hom Q X) (q' : Hom Q Y)
    (H1 : p' ∘ i.1 ≈ p) (H2 : q' ∘ i.1 ≈ q)
  : is_product X Y Q p' q'.
Proof.
  intros Z f g. destruct (HP Z f g) as [h [Hh Hu]].
  exists (i.1 ∘ h). refine {|this := _
                          ; that := _
                          |}.
  - split; rewrite <- comp_assoc;
      [rewrite H1; exact (fst Hh) | rewrite H2; exact (snd Hh)].
  - intros k [K1 K2].
    assert (K : i.2.1 ∘ k ≈ h).
    { apply Hu. split; [rewrite <- H1 | rewrite <- H2];
        rewrite !comp_assoc, <- (comp_assoc i.1),
          (snd i.2.2), comp_id_l; assumption. }
    rewrite <- K, <- comp_assoc, (snd i.2.2), comp_id_l. reflexivity.
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

(** Equality of product-valued arrows is exactly equality of projections. *)

(** 积值箭头相等当且仅当两个投影相等。 *)

Lemma product_eq_iff {C : Cat} `{HP : !HasProduct C}
    {X Y Z : @Ob C} (f g : Hom Z (X × Y))
  : f ≈ g ↔ (π1 ∘ f ≈ π1 ∘ g ∧ π2 ∘ f ≈ π2 ∘ g).
Proof.
  split.
  - intros H. split; rewrite H; reflexivity.
  - intros [H1 H2]. exact (product_cone_ext product_universal H1 H2).
Qed.

(** Pairing the two projections is the identity. *)

(** 两个投影的配对为恒等。 *)

Lemma product_pair_η {C : Cat} `{HP : !HasProduct C} {X Y : @Ob C}
  : ⟨(π1 : Hom (X × Y) X), π2⟩ ≈ id.
Proof. symmetry. apply product_pair_unique. split; apply comp_id_r. Qed.

(** Reassociate a triple product using only its projections and pairings. *)

(** 仅用投影及配对改变三重积的括号。 *)

Definition product_assoc {C : Cat} `{HP : !HasProduct C} {X Y Z : @Ob C}
  : ((X × Y) × Z) ≅ (X × (Y × Z)).
Proof.
  exists ⟨π1 ∘ π1, ⟨π2 ∘ π1, π2⟩⟩,
    ⟨⟨π1, π1 ∘ π2⟩, π2 ∘ π2⟩.
  split; unfold is_linv_of, is_rinv_of;
    repeat first [rewrite product_comp_r | rewrite comp_assoc |
      rewrite product_β1 | rewrite product_β2];
    rewrite <- !product_comp_r, !product_pair_η, !comp_id_l;
    apply product_pair_η.
Defined.

(** The associator sends a nested pairing to the other bracketing. *)

(** 结合同构将嵌套配对送到另一种括号形式。 *)

Lemma product_assoc_pair {C : Cat} `{HP : !HasProduct C}
    {W X Y Z : @Ob C} (f : Hom W X) (g : Hom W Y) (h : Hom W Z)
  : (@product_assoc C HP X Y Z).1 ∘ ⟨⟨f, g⟩, h⟩ ≈ ⟨f, ⟨g, h⟩⟩.
Proof.
  cbn. rewrite !product_comp_r, !comp_assoc, !product_β1, !product_β2.
  reflexivity.
Qed.

(** Reassociate and exchange the last two factors. This is the context
    permutation used by iterated currying. *)

(** 改变括号并交换后两个因子；此上下文置换用于迭代柯里化。 *)

Definition product_exchange {C : Cat} `{HP : !HasProduct C}
    {X Y Z : @Ob C}
  : ((X × Y) × Z) ≅ (X × (Z × Y)).
Proof.
  exists ⟨π1 ∘ π1, ⟨π2, π2 ∘ π1⟩⟩,
    ⟨⟨π1, π2 ∘ π2⟩, π1 ∘ π2⟩.
  split; unfold is_linv_of, is_rinv_of;
    repeat first [rewrite product_comp_r | rewrite comp_assoc |
      rewrite product_β1 | rewrite product_β2];
    rewrite <- !product_comp_r, !product_pair_η, !comp_id_l;
    apply product_pair_η.
Defined.

(** The context permutation is natural in each of its three factors. *)

(** 上下文置换在三个因子上分别自然。 *)

Lemma product_exchange_natural {C : Cat} `{HP : !HasProduct C}
    {X Y Z X' Y' Z' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z')
  : (@product_exchange C HP X' Y' Z').1 ∘ ((f × g) × h) ≈
      (f × (h × g)) ∘ (@product_exchange C HP X Y Z).1.
Proof.
  cbn. repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2].
  reflexivity.
Qed.

(** The inverse context permutation has the corresponding naturality law. *)

(** 逆上下文置换具有对应的自然性定律。 *)

Lemma product_exchange_inv_natural {C : Cat} `{HP : !HasProduct C}
    {X Y Z X' Y' Z' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z')
  : ((f × g) × h) ∘ (@product_exchange C HP X Y Z).2.1 ≈
      (@product_exchange C HP X' Y' Z').2.1 ∘ (f × (h × g)).
Proof.
  cbn. repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2].
  reflexivity.
Qed.
