From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Pullback
  Cat.Morphism
  Cat.Subobject.

(** * Pulling Back Along a Product Projection

    Binary products supply the pullback of any arrow along first
    projection. Keep that product and its pairing mediator; no selected
    pullback structure is needed. *)

(** * 沿积投影拉回

    二元积给出任意箭头沿第一投影的拉回。保留该积及配对中介，不要求选定
    拉回结构。 *)

(** The product map and first projection form the required candidate
    pullback, using the original product universal property. *)

(** 积映射与第一投影使用原积泛性质形成所需的候选拉回。 *)

Definition product_projection_pullback {C : Cat} `{HP : !HasProduct C}
    {X Y : C} (m : Hom Y X) (A : C)
  : is_pullback (π1 : Hom (X × A) X) m (Y × A) (m × id) π1.
Proof.
  split.
  - rewrite cross_η, product_β1. reflexivity.
  - intros Q q r Hq. exists ⟨r, π2 ∘ q⟩. split.
    + split.
      * rewrite product_comp_l, comp_id_l, <- Hq.
        symmetry. apply product_η.
      * apply product_β1.
    + intros k [Hk Hr]. apply product_pair_unique. split.
      * exact Hr.
      * transitivity (π2 ∘ ((m × id) ∘ k)).
        -- rewrite <- comp_assoc, cross_η, product_β2, comp_id_l.
           reflexivity.
        -- rewrite Hk. reflexivity.
Defined.

(** The same square displays the inverse image of a subobject as its
    product with the unchanged second factor. *)

(** 同一方形将子对象的逆像展示为它与未改变的第二因子的积。 *)

Program Definition SubProduct {C : Cat} `{HP : !HasProduct C}
    {X : C} (s : Sub X) (A : C)
  : Sub (X × A)
  :=
  {|sub := sub s × A
  ; sub_mono := PullbackMono (product_projection_pullback s A)
  |}.
