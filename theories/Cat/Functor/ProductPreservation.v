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

Local Open Scope ob_scope.

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
Context (preserves : ∀ X Y : C,
    is_product (F X) (F Y) (F (X × Y)) (fmap F π1) (fmap F π2)).

(** Preservation of the chosen cones extends to any candidate product.
    Transport through its canonical apex isomorphism; no target product
    choice, terminal structure or equality of witnesses is needed. *)

(** 选定锥的保持性推广到任意候选积。沿规范顶点同构运输，不需要目标积
    选择、终对象结构或见证相等。 *)

Definition preserved_product_cone {X Y P : C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
  : is_product (F X) (F Y) (F P) (fmap F p) (fmap F q).
Proof.
  pose (i := product_unique (@product_universal C PC X Y) HP).
  refine (product_apex_iso (preserves X Y)
    (fmap F i.1; fct_is_iso F i.1 i.2) (fmap F p) (fmap F q) _ _).
  - change (fmap F p ∘ fmap F i.1 ≈ fmap F π1).
    rewrite <- fct_comp. apply fct_fmap_proper.
    exact (fst (this (HP _ π1 π2).2)).
  - change (fmap F q ∘ fmap F i.1 ≈ fmap F π2).
    rewrite <- fct_comp. apply fct_fmap_proper.
    exact (snd (this (HP _ π1 π2).2)).
Defined.

(** The two product universal properties determine the canonical isomorphism. *)

(** 两个积泛性质确定规范同构。 *)

Definition preserved_product_iso (X Y : C)
  : F (X × Y) ≅ (F X × F Y)
  := product_unique (preserves X Y) product_universal.

(** The inverse comparison is the mediator into the image product cone. *)

(** 逆比较是指向像积锥的中介。 *)

Definition preserved_product_inv (X Y : C)
  : Hom (F X × F Y) (F (X × Y))
  := (preserves X Y _ π1 π2).1.

(** Its projections are the chosen target projections in specified equality. *)

(** 按指定相等，其两个投影就是选定的目标投影。 *)

Lemma preserved_product_inv_β (X Y : C)
  : (fmap F π1 ∘ preserved_product_inv X Y ≈ π1) ∧
    (fmap F π2 ∘ preserved_product_inv X Y ≈ π2).
Proof. exact (this (preserves X Y _ π1 π2).2). Qed.

(** The image pairing factors through the inverse comparison. *)

(** 配对的像通过逆比较分解。 *)

Lemma preserved_pair {X Y Z : C} (f : Hom Z X) (g : Hom Z Y)
  : fmap F ⟨f, g⟩ ≈ preserved_product_inv X Y ∘ ⟨fmap F f, fmap F g⟩.
Proof.
  apply (product_cone_ext (preserves X Y)).
  - rewrite <- !comp_assoc, <- fct_comp, product_β1,
      (fst (preserved_product_inv_β X Y)), product_β1. reflexivity.
  - rewrite <- !comp_assoc, <- fct_comp, product_β2,
      (snd (preserved_product_inv_β X Y)), product_β2. reflexivity.
Qed.

(** The inverse comparison is natural in both factors. *)

(** 逆比较在两个因子上自然。 *)

Lemma preserved_product_inv_natural {X Y X' Y' : C}
    (f : Hom X X') (g : Hom Y Y')
  : fmap F (f × g) ∘ preserved_product_inv X Y ≈
      preserved_product_inv X' Y' ∘ (fmap F f × fmap F g).
Proof.
  apply (product_cone_ext (preserves X' Y')).
  - rewrite <- !comp_assoc, <- fct_comp, cross_η, product_β1,
      fct_comp, comp_assoc, (fst (preserved_product_inv_β X Y)),
      (fst (preserved_product_inv_β X' Y')), cross_η, product_β1.
    reflexivity.
  - rewrite <- !comp_assoc, <- fct_comp, cross_η, product_β2,
      fct_comp, comp_assoc, (snd (preserved_product_inv_β X Y)),
      (snd (preserved_product_inv_β X' Y')), cross_η, product_β2.
    reflexivity.
Qed.

End ProductPreservation.

(** ** Composition with Binary Products Only

    Fix three categories with independently chosen products and two
    functors preserving their source cones. Candidate preservation gives
    the composite cones. Its inverse comparison is independent, up to
    specified equality, of the supplied composite preservation witness. *)

(** ** 只依赖二元积的复合

    固定三个具有独立积选择的范畴及两个保持来源锥的函子。候选保持性给出
    复合锥。按指定相等，复合的逆比较不依赖另给的复合保持见证。 *)

Section ProductComposition.
Context {C D E : Cat} (F : Fct C D) (G : Fct D E).
Context `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F (X × Y)) (fmap F π1) (fmap F π2)).
Context (preservesG : ∀ X Y : D,
    is_product (G X) (G Y) (G (X × Y)) (fmap G π1) (fmap G π2)).

(** Choose the composite candidate by the existing apex transport. There
    is no new choice of products or implicit preservation instance. *)

(** 通过既有顶点运输给出复合候选，不另选积，也不隐式注册保持实例。 *)

Definition preserved_product_comp (X Y : C)
  : is_product ((G ∘F F) X) ((G ∘F F) Y)
      ((G ∘F F) (X × Y))
      (fmap (G ∘F F) π1) (fmap (G ∘F F) π2)
  := preserved_product_cone G preservesG (preservesF X Y).

Context `{PE : !HasProduct E}.
Context (preservesGF : ∀ X Y : C,
    is_product ((G ∘F F) X) ((G ∘F F) Y)
      ((G ∘F F) (X × Y))
      (fmap (G ∘F F) π1) (fmap (G ∘F F) π2)).

(** Any supplied composite witness has the same inverse comparison as
    the two consecutive comparisons. The witnesses need not be equal. *)

(** 任意指定复合见证的逆比较均与连续两次比较相等，无需见证本身相等。 *)

Lemma preserved_product_inv_comp (X Y : C)
  : preserved_product_inv (G ∘F F) preservesGF X Y ≈
      fmap G (preserved_product_inv F preservesF X Y) ∘
        preserved_product_inv G preservesG (F X) (F Y).
Proof.
  symmetry. apply (preservesGF X Y _ π1 π2).2. split.
  - change (fmap G (fmap F π1) ∘
      (fmap G (preserved_product_inv F preservesF X Y) ∘
        preserved_product_inv G preservesG (F X) (F Y)) ≈ π1).
    rewrite <- comp_assoc, <- fct_comp,
      (fst (preserved_product_inv_β F preservesF X Y)).
    exact (fst (preserved_product_inv_β G preservesG (F X) (F Y))).
  - change (fmap G (fmap F π2) ∘
      (fmap G (preserved_product_inv F preservesF X Y) ∘
        preserved_product_inv G preservesG (F X) (F Y)) ≈ π2).
    rewrite <- comp_assoc, <- fct_comp,
      (snd (preserved_product_inv_β F preservesF X Y)).
    exact (snd (preserved_product_inv_β G preservesG (F X) (F Y))).
Defined.

End ProductComposition.
