From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Export
  Cat.Limit.Core
  Cat.Diagram.Discrete.

(** * Indexed Products as Discrete Limits

    The chosen structure is [HasLimit C (DiscreteF D)]. No second copy of its
    universal property, mediator, or coherence laws is stored. *)

(** * 索引积作为离散极限

    选定结构是 [HasLimit C (DiscreteF D)]；不重复保存泛性质、中介或相干律。 *)

Notation "'∏[' D ']'" := (Lim (DiscreteF D)) : ob_scope.

(** ** Laws of an Indexed Product

    Fix an [I]-indexed object family [D] and a chosen limit of its discrete
    diagram. Extract projections and tupling, then derive their computation
    and uniqueness laws. *)

(** ** 指标积的定律

    固定以 [I] 为指标的对象族 [D] 及其离散图式的选定极限，提取投影和组元组操作，再导出计算及唯一性定律。 *)

Section IndexedProduct.
Context {C : Cat} {I : Type} {D : I → @Ob C}
    `{HP : !HasLimit C (DiscreteF D)}.

(** The projection of an indexed product, obtained from its discrete limiting
    cone. *)

(** 从离散极限锥提取的索引积投影。 *)

Definition indexed_proj (i : I)
  : Hom ∏[D] (D i)
  := πlim[DiscreteF D] i.

(** The universal arrow assembling an indexed family of components. *)

(** 组装索引分量族的泛箭头。 *)

Definition indexed_pair {X : @Ob C} (κ : ∀ i, Hom X (D i))
  : Hom X ∏[D]
  := @limit_lift (DiscreteCat I) C (DiscreteF D) HP X
    (@DiscreteCone C I (DiscreteF D) X κ).

(** Projecting an indexed pairing recovers the corresponding component. *)

(** 投影索引配对，恢复对应分量。 *)

Lemma indexed_product_β {X : @Ob C} (κ : ∀ i, Hom X (D i)) (i : I)
  : indexed_proj i ∘ indexed_pair κ ≈ κ i.
Proof.
  exact (@limit_β (DiscreteCat I) C (DiscreteF D) HP X
    (@DiscreteCone C I (DiscreteF D) X κ) i).
Qed.

(** An arrow to an indexed product is recovered from all its projections. *)

(** 指向索引积的箭头由全部投影恢复。 *)

Lemma indexed_product_η {X : @Ob C} (f : Hom X ∏[D])
  : indexed_pair (λ i, indexed_proj i ∘ f) ≈ f.
Proof.
  transitivity (lim⟨πlim[DiscreteF D] ∘Cone f⟩).
  - apply limit_lift_proper. intros i. reflexivity.
  - apply limit_η.
Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance indexed_pair_proper {X : @Ob C}
  : Proper ((λ κ μ : ∀ i, Hom X (D i), ∀ i, κ i ≈ μ i) ==>
      @HomEq C X ∏[D]) indexed_pair.
Proof. intros κ μ H. apply limit_lift_proper. exact H. Qed.

(** Precomposition of indexed pairing acts componentwise. *)

(** 索引配对的预合成逐分量作用。 *)

Lemma indexed_product_comp {X Y : @Ob C} (κ : ∀ i, Hom X (D i)) (f : Hom Y X)
  : indexed_pair κ ∘ f ≈ indexed_pair (λ i, κ i ∘ f).
Proof.
  unfold indexed_pair. rewrite <- limit_lift_comp.
  apply limit_lift_proper. intros i. reflexivity.
Qed.

(** All indexed projections together detect equality of product-valued arrows. *)

(** 全部索引投影共同检测积值箭头相等。 *)

Theorem indexed_product_hom_ext {X : @Ob C} (f g : Hom X ∏[D])
    (H : ∀ i, indexed_proj i ∘ f ≈ indexed_proj i ∘ g)
  : f ≈ g.
Proof.
  rewrite <- (indexed_product_η f), <- (indexed_product_η g).
  apply indexed_pair_proper. exact H.
Qed.

End IndexedProduct.

Notation "'π∏[' D ']'" := (indexed_proj (D := D)) : hom_scope.
Notation "'∏⟨' κ '⟩'" := (indexed_pair κ) : hom_scope.
