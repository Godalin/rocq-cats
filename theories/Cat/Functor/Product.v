From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Product.Core.

(** * Comparisons for Preserved Products

    Only specified product cones are needed, without terminal objects. *)

(** * 保持积的比较

    仅需指定积锥，无需终对象。 *)

Local Open Scope hom_scope.

Section PreservedProducts.
Context {C D : Cat} (F : Functor C D)
    `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context (HP : ∀ X Y, is_product (F X) (F Y) (F ((X × Y)%ob))
    (fmap F (@Cats.Cat.Product.Core.π1 C PC X Y))
    (fmap F (@Cats.Cat.Product.Core.π2 C PC X Y))).

(** The canonical comparison retains both universal mediators. *)

(** 规范比较保留两个泛中介。 *)

Definition PreservedProductIso (X Y : @Ob C)
  : F ((X × Y)%ob) ≅ (F X × F Y)%ob
  := product_unique (HP X Y) (@product_universal D PD (F X) (F Y)).

(** The inverse is the mediator into the preserved cone. *)

(** 逆映射是进入保持锥的中介。 *)

Definition preserved_product_inv (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := (HP X Y _ π1 π2).1.

(** The inverse comparison has both specified projections. *)

(** 逆比较具有两个指定投影。 *)

Lemma preserved_product_inv_β (X Y : @Ob C)
  : (fmap F π1 ∘ preserved_product_inv X Y ≈ π1) ∧
    (fmap F π2 ∘ preserved_product_inv X Y ≈ π2).
Proof. exact (@this _ _ _ _ _ (HP X Y _ π1 π2).2). Qed.

(** Inverse comparison is natural without additional structure choices. *)

(** 逆比较的自然性无需额外结构选择。 *)

Lemma preserved_product_inv_natural {X Y X' Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : fmap F (f × g) ∘ preserved_product_inv X Y ≈
      preserved_product_inv X' Y' ∘ (fmap F f × fmap F g).
Proof.
  transitivity ((HP X' Y' _ (fmap F f ∘ π1) (fmap F g ∘ π2)).1).
  - apply (HP X' Y' _ _ _).2. split;
      rewrite <- comp_assoc, <- functor_comp, cross_η;
      [rewrite product_β1 | rewrite product_β2];
      rewrite functor_comp, comp_assoc;
      [rewrite (fst (preserved_product_inv_β X Y)) |
       rewrite (snd (preserved_product_inv_β X Y))]; reflexivity.
  - symmetry. apply (HP X' Y' _ _ _).2. split;
      rewrite <- comp_assoc;
      [rewrite (fst (preserved_product_inv_β X' Y')), cross_η, product_β1 |
       rewrite (snd (preserved_product_inv_β X' Y')), cross_η, product_β2];
      reflexivity.
Qed.

End PreservedProducts.
