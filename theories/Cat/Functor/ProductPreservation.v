From Cats Require Export Cat.Functor.Core.
From Cats Require Import
  Cat.Core
  Cat.Product.Transport.

(** * Comparisons from Binary-Product Preservation

    Preservation is supplied as a family of candidate universal properties.
    No terminal object or terminal preservation is needed. The comparison
    maps use the original transparent product mediators. *)

(** * 从二元积保持性得到比较

    保持性以一族候选泛性质给出，不需要终对象或终对象保持性。比较映射使用
    原有的透明积中介。 *)

(** ** Comparing Chosen Products

    Fix chosen binary products in both categories and a functor preserving
    the source cones. Construct their canonical comparison and derive its
    pairing and naturality equations using only these cones. *)

(** ** 比较选定积

    固定两侧的选定二元积和保持来源锥的函子。仅用这些锥构造规范比较，并
    导出配对和自然性方程。 *)

Section ProductPreservation.
Context {C D : Cat} (F : Fct C D).
Context `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context (preserves : ∀ X Y : @Ob C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** The two product universal properties determine the canonical isomorphism. *)

(** 两个积泛性质确定规范同构。 *)

Definition preserved_product_iso (X Y : @Ob C)
  : F ((X × Y)%ob) ≅ (F X × F Y)%ob
  := product_unique (preserves X Y) product_universal.

(** The inverse comparison is the mediator into the image product cone. *)

(** 逆比较是指向像积锥的中介。 *)

Definition preserved_product_inv (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := (preserves X Y _ π1 π2).1.

(** Its projections are the chosen target projections in specified equality. *)

(** 按指定相等，其两个投影就是选定的目标投影。 *)

Lemma preserved_product_inv_β (X Y : @Ob C)
  : (fmap F π1 ∘ preserved_product_inv X Y ≈ π1) ∧
    (fmap F π2 ∘ preserved_product_inv X Y ≈ π2).
Proof. exact (@this _ _ _ _ _ (preserves X Y _ π1 π2).2). Qed.

(** The image pairing factors through the inverse comparison. *)

(** 配对的像通过逆比较分解。 *)

Lemma preserved_pair {X Y Z : @Ob C} (f : Hom Z X) (g : Hom Z Y)
  : fmap F ⟨f, g⟩ ≈ preserved_product_inv X Y ∘ ⟨fmap F f, fmap F g⟩.
Proof.
  apply (product_cone_ext (preserves X Y)).
  - rewrite <- !comp_assoc, <- functor_comp, product_β1,
      (fst (preserved_product_inv_β X Y)), product_β1. reflexivity.
  - rewrite <- !comp_assoc, <- functor_comp, product_β2,
      (snd (preserved_product_inv_β X Y)), product_β2. reflexivity.
Qed.

(** The inverse comparison is natural in both factors. *)

(** 逆比较在两个因子上自然。 *)

Lemma preserved_product_inv_natural {X Y X' Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : fmap F (f × g) ∘ preserved_product_inv X Y ≈
      preserved_product_inv X' Y' ∘ (fmap F f × fmap F g).
Proof.
  apply (product_cone_ext (preserves X' Y')).
  - rewrite <- !comp_assoc, <- functor_comp, cross_η, product_β1,
      functor_comp, comp_assoc, (fst (preserved_product_inv_β X Y)),
      (fst (preserved_product_inv_β X' Y')), cross_η, product_β1.
    reflexivity.
  - rewrite <- !comp_assoc, <- functor_comp, cross_η, product_β2,
      functor_comp, comp_assoc, (snd (preserved_product_inv_β X Y)),
      (snd (preserved_product_inv_β X' Y')), cross_η, product_β2.
    reflexivity.
Qed.

End ProductPreservation.
