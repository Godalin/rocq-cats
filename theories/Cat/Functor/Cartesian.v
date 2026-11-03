From Cats Require Export Cat.Functor.Core.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core.

(** * Functors Preserving Finite Products

    Preservation concerns full universal properties. The canonical comparison
    and its inverse are derived, without equality of chosen objects. *)

(** * 保持有限积的函子

    保持性使用完整泛性质；规范比较及其逆由此导出，不要求选定对象原生相等。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

(** Preserve the selected terminal and binary-product cones as full cones. *)

(** 将选定终对象与二元积锥保持为具有完整泛性质的锥。 *)

Class IsCartesianF {C D : Cat} (F : Functor C D)
    (TC : HasTerminal C) (PC : HasProduct C)
  :=
  { functor_terminal : is_terminal (F (@Term C TC))
  ; functor_product X Y : is_product (F X) (F Y)
      (F (@Prod C PC X Y)) (fmap F (@Cats.Cat.Product.Core.π1 C PC X Y))
      (fmap F (@Cats.Cat.Product.Core.π2 C PC X Y))
  }.

Section CartesianFunctor.
Context {C D : Cat} (F : Functor C D)
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{TD : !HasTerminal D} `{PD : !HasProduct D}
    `{HF : !IsCartesianF F TC PC}.

(** The image product and the chosen target product are canonically isomorphic. *)

(** 像积与目标选定积之间具有规范同构。 *)

Definition functor_product_iso (X Y : @Ob C)
  : F ((X × Y)%ob) ≅ (F X × F Y)%ob.
Proof.
  exact (product_unique (functor_product X Y) (@product_universal D PD (F X) (F Y))).
Defined.

(** The inverse comparison is the mediator of the preserved product. *)

(** 逆向比较是保持积的泛中介。 *)

Definition functor_product_inv (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := (functor_product X Y _ π1 π2).1.

(** Both projections of the inverse comparison compute. *)

(** 逆向比较的两个投影均满足计算方程。 *)

Lemma functor_product_inv_β (X Y : @Ob C)
  : (fmap F π1 ∘ functor_product_inv X Y ≈ π1) ∧
    (fmap F π2 ∘ functor_product_inv X Y ≈ π2).
Proof. exact (@this _ _ _ _ _ (functor_product X Y _ π1 π2).2). Qed.

(** Pairing is preserved through the product comparison. *)

(** 配对通过积比较得到保持。 *)

Lemma functor_pair {X Y Z : @Ob C} (f : Hom Z X) (g : Hom Z Y)
  : fmap F ⟨f, g⟩ ≈ functor_product_inv X Y ∘ ⟨fmap F f, fmap F g⟩.
Proof.
  transitivity ((functor_product X Y _ (fmap F f) (fmap F g)).1).
  - apply (functor_product X Y _ (fmap F f) (fmap F g)).2.
    split; rewrite <- functor_comp; [rewrite product_β1 | rewrite product_β2];
      reflexivity.
  - symmetry. apply (functor_product X Y _ (fmap F f) (fmap F g)).2.
    split; rewrite <- comp_assoc;
      [rewrite (fst (functor_product_inv_β X Y)), product_β1 |
       rewrite (snd (functor_product_inv_β X Y)), product_β2]; reflexivity.
Qed.

(** The inverse comparison is natural in both factors. *)

(** 逆向比较在两个因子上自然。 *)

Lemma functor_product_inv_natural {X Y X' Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : fmap F (f × g) ∘ functor_product_inv X Y ≈
      functor_product_inv X' Y' ∘ (fmap F f × fmap F g).
Proof.
  transitivity ((functor_product X' Y' _
    (fmap F f ∘ π1) (fmap F g ∘ π2)).1).
  - apply (functor_product X' Y' _ _ _).2. split;
      rewrite <- comp_assoc, <- functor_comp, cross_η;
      [rewrite product_β1 | rewrite product_β2];
      rewrite functor_comp, comp_assoc;
      [rewrite (fst (functor_product_inv_β X Y)) |
       rewrite (snd (functor_product_inv_β X Y))]; reflexivity.
  - symmetry. apply (functor_product X' Y' _ _ _).2. split;
      rewrite <- comp_assoc;
      [rewrite (fst (functor_product_inv_β X' Y')), cross_η, product_β1 |
       rewrite (snd (functor_product_inv_β X' Y')), cross_η, product_β2];
      reflexivity.
Qed.

End CartesianFunctor.

(** Identity functors preserve every selected finite-product structure. *)

(** 恒等函子保持任意选定有限积结构。 *)

Program Definition IdF_IsCartesianF (C : Cat)
    (TC : HasTerminal C) (PC : HasProduct C)
  : IsCartesianF (@IdF C) TC PC
  :=
  {|functor_terminal := @terminal_universal C TC
  ; functor_product := @product_universal C PC
  |}.

(** The identity functor's inverse product comparison is the identity arrow. *)

(** 恒等函子的逆向积比较等于恒等箭头。 *)

Lemma id_functor_product_inv (C : Cat) (TC : HasTerminal C)
    (PC : HasProduct C) (X Y : @Ob C)
  : @functor_product_inv C C (@IdF C) TC PC PC
      (IdF_IsCartesianF C TC PC) X Y ≈ id.
Proof.
  symmetry. apply product_pair_unique. split; apply comp_id_r.
Qed.
