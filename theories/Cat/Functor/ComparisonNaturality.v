From Cats Require Export
  Cat.Functor.ExponentialComparison.
From Cats Require Import
  Cat.Core
  Cat.Natural
  Cat.Product.Transport
  Cat.Exponential.Core
  Cat.Exponential.Functor.

(** * Naturality of Product and Exponential Comparisons

    Reuse the existing comparison maps, assuming only binary-product
    preservation. Natural transformations respect the inverse product
    comparisons. Exponential comparisons are natural in their argument
    and result, and compatible with a natural transformation through a
    mixed exponential. No terminal objects, exponential preservation or
    invertibility of the transformation are required. *)

(** * 积与指数比较的自然性

    只假设二元积保持，复用已有比较映射。自然变换与逆积比较相容；指数比较
    对参数及结果自然，并通过混合指数与自然变换相容。不要求终对象、指数
    保持性或自然变换可逆。 *)

(** ** A Natural Boundary between Product-Preserving Functors

    Fix two functors with the same source and target, named product
    choices and preservation witnesses. Naturality at both projections
    identifies their inverse comparisons by image-product uniqueness. *)

(** ** 保积函子之间的自然边界

    固定同源同目标的两个函子、具名积选择及保持见证。两个投影处的自然性
    通过像积唯一性确定逆比较的相容性。 *)

Section ProductBoundary.
Context {C D : Cat} (F G : Fct C D).
Context `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).
Context (preservesG : ∀ X Y : C,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).
Context (α : F ⇒ G).

(** The same component family commutes with both product comparisons;
    there is no equality of product objects or universal witnesses. *)

(** 同一分量族与两个积比较交换，不要求积对象或泛见证相等。 *)

Lemma preserved_product_inv_boundary (X Y : C)
  : α ((X × Y)%ob) ∘ preserved_product_inv F preservesF X Y ≈
      preserved_product_inv G preservesG X Y ∘ (α X × α Y).
Proof.
  apply (product_cone_ext (preservesG X Y)).
  - rewrite <- !comp_assoc, <- (nt_naturality α π1), comp_assoc,
      (fst (preserved_product_inv_β F preservesF X Y)),
      (fst (preserved_product_inv_β G preservesG X Y)), cross_η, product_β1.
    reflexivity.
  - rewrite <- !comp_assoc, <- (nt_naturality α π2), comp_assoc,
      (snd (preserved_product_inv_β F preservesF X Y)),
      (snd (preserved_product_inv_β G preservesG X Y)), cross_η, product_β2.
    reflexivity.
Defined.

End ProductBoundary.

(** ** Changing the Exponential Argument and Result

    Fix products and exponentials in both categories, with binary-product
    preservation by one functor. The same evaluation and currying laws
    make its comparison natural in both variables. *)

(** ** 改变指数参数与结果

    固定两个范畴中的积及指数，并给出一个函子的二元积保持性；原有求值和
    柯里化定律使其比较在两个变量上自然。 *)

Section ExponentialNaturality.
Context {C D : Cat} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ X Y : C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** Argument change is contravariant and result change covariant, with
    their original arrow actions retained on either side. *)

(** 参数变换反变而结果变换协变，两侧均保留原有箭头作用。 *)

Lemma preserved_exponential_natural {X X' Y Y' : C}
    (u : Hom X' X) (v : Hom Y Y')
  : preserved_exponential_comparison F preserves X' Y' ∘ fmap F (v ^ u) ≈
      (fmap F v ^ fmap F u) ∘
        preserved_exponential_comparison F preserves X Y.
Proof.
  unfold exponential_dimap at 1. rewrite preserved_curry.
  symmetry. apply exponential_curry_unique.
  change (uncurry ((fmap F v ^ fmap F u) ∘
      preserved_exponential_comparison F preserves X Y) ≈
    fmap F (v ∘ eval ∘ (id × u)) ∘
      preserved_product_inv F preserves ((Y ^ X)%ob) X').
  rewrite exponential_uncurry_dimap.
  unfold uncurry. rewrite (preserved_eval F preserves X Y).
  pose proof (preserved_product_inv_natural F preserves
    (@id ((Y ^ X)%ob)) u) as HP.
  rewrite (@functor_id C D F) in HP.
  rewrite !(@functor_comp C D F), !(@comp_assoc D), HP. reflexivity.
Defined.

End ExponentialNaturality.

(** ** A Natural Boundary and the Mixed Exponential

    Give both functors' binary-product preservation. Compare maps from
    [F (Y ^ X)] to [G Y ^ F X]: change the result through [α Y], or
    change the represented object through [α (Y ^ X)] and restrict the
    argument along [α X]. This is a mixed-endpoint equation, not a
    covariant action on both exponential variables. *)

(** ** 自然边界及混合指数

    给出两个函子的二元积保持性。比较从 [F (Y ^ X)] 到 [G Y ^ F X]
    的映射：沿 [α Y] 改变结果，或者先沿 [α (Y ^ X)] 改变表示对象，再沿
    [α X] 限制参数。这是混合端点方程，不是对两个指数变量都协变的作用。 *)

Section ExponentialBoundary.
Context {C D : Cat} (F G : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).
Context (preservesG : ∀ X Y : C,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).
Context (α : F ⇒ G).

(** Naturality of evaluation and the preceding product-boundary law
    establish compatibility without an inverse of any component. *)

(** 求值的自然性及前述积边界律给出相容性，无需任何分量的逆。 *)

Lemma preserved_exponential_boundary (X Y : C)
  : (α Y ^ (@id (F X))) ∘
      preserved_exponential_comparison F preservesF X Y ≈
      ((@id (G Y)) ^ α X) ∘
        preserved_exponential_comparison G preservesG X Y ∘
        α ((Y ^ X)%ob).
Proof.
  apply exponential_ext.
  change (uncurry ((α Y ^ (@id (F X))) ∘
      preserved_exponential_comparison F preservesF X Y) ≈
    uncurry (((@id (G Y)) ^ α X) ∘
      preserved_exponential_comparison G preservesG X Y ∘
      α ((Y ^ X)%ob))).
  rewrite (comp_assoc (((@id (G Y)) ^ α X))
    (preserved_exponential_comparison G preservesG X Y)
    (α ((Y ^ X)%ob))).
  rewrite !exponential_uncurry_dimap, exponential_uncurry_comp_r.
  unfold uncurry.
  rewrite (preserved_eval F preservesF X Y),
    (preserved_eval G preservesG X Y), cross_id, comp_id_r, comp_id_l.
  rewrite !(@comp_assoc D), <- cross_comp, comp_id_r, comp_id_l.
  rewrite <- (comp_assoc (α Y) (fmap F eval)
    (preserved_product_inv F preservesF ((Y ^ X)%ob) X)).
  rewrite (nt_naturality α eval), comp_assoc,
    (preserved_product_inv_boundary F G preservesF preservesG α).
  reflexivity.
Defined.

End ExponentialBoundary.
