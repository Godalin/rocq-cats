From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Isomorphism
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Exponential.Core.

(** * Exponentials and Fully Faithful Functors

    Only chosen products and preservation of their cones are required.
    Essential surjectivity is needed for preservation, but not reflection. *)

(** * 指数与全忠实函子

    仅要求选定积及其锥的保持性；保持指数需要本质满性，反映指数则不需要。 *)

Local Open Scope hom_scope.

Section ExponentialImages.
Context {C D : Cat} (F : Functor C D)
    `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context (HP : ∀ X Y, is_product (F X) (F Y) (F ((X × Y)%ob))
    (fmap F (@Cats.Cat.Product.Core.π1 C PC X Y))
    (fmap F (@Cats.Cat.Product.Core.π2 C PC X Y))).

(** Image evaluation first uses the inverse product comparison. *)

(** 像求值首先使用逆向积比较。 *)

Definition exponential_image_eval {X Y E : @Ob C} (ev : Hom (E × X) Y)
  : Hom (F E × F X) (F Y)
  := fmap F ev ∘ preserved_product_inv F HP E X.

(** Uncurrying an image arrow agrees with mapping its original evaluation,
    after the inverse product comparison. *)

(** 像箭头的反柯里化等于原求值的函子像与逆向积比较的复合。 *)

Lemma exponential_image_uncurry {X Y E Z : @Ob C}
    (ev : Hom (E × X) Y) (h : Hom Z E)
  : exponential_image_eval ev ∘ (fmap F h × id) ≈
      fmap F (ev ∘ (h × id)) ∘ preserved_product_inv F HP Z X.
Proof.
  unfold exponential_image_eval.
  pose proof (preserved_product_inv_natural F HP h
    (@Cats.Cat.Core.id C X)) as H.
  rewrite functor_id in H.
  rewrite comp_assoc, <- H, <- comp_assoc, <- functor_comp. reflexivity.
Qed.

(** Fullness lifts the target transpose; faithfulness and invertible
    product comparisons reflect its full universal property. *)

(** 满性提升目标转置；忠实性与可逆积比较反映其完整泛性质。 *)

Definition fully_faithful_reflects_exponential
    (HF : is_fully_faithful F) {X Y E : @Ob C}
    (ev : Hom (E × X) Y)
    (HE : is_exponential (F X) (F Y) (F E) (exponential_image_eval ev))
  : is_exponential X Y E ev.
Proof.
  intros Z f.
  destruct (HE (F Z) (fmap F f ∘ preserved_product_inv F HP Z X))
    as [h [Hh Hu]].
  destruct (fst HF Z E h) as [g Hg].
  exists g. refine {|this := _
                   ; that := _
                   |}.
  - apply (snd HF).
    apply (iso_cancel_r (iso_symm (PreservedProductIso F HP Z X))).
    rewrite <- exponential_image_uncurry, Hg. exact Hh.
  - intros k Hk. apply (snd HF). transitivity h; [| symmetry; exact Hg].
    apply Hu. rewrite exponential_image_uncurry, Hk. reflexivity.
Defined.

(** At image objects, full faithfulness alone preserves the unique
    transpose. The remaining objects are handled by representatives below. *)

(** 在像对象处，仅全忠实性就保持唯一转置；其他对象由下文的代表处理。 *)

Definition fully_faithful_exponential_at_image
    (HF : is_fully_faithful F) {X Y E : @Ob C}
    (ev : Hom (E × X) Y) (HE : is_exponential X Y E ev)
    (Z : @Ob C) (f : Hom (F Z × F X) (F Y))
  : ∃ h : Hom (F Z) (F E),
      is_unique (λ h, exponential_image_eval ev ∘ (h × id) ≈ f) h.
Proof.
  pose (i := PreservedProductIso F HP Z X).
  destruct (fst HF _ _ (f ∘ i.1)) as [g Hg].
  destruct (HE Z g) as [h [Hh Hu]].
  exists (fmap F h). refine {|this := _
                            ; that := _
                            |}.
  - rewrite exponential_image_uncurry, Hh, Hg.
    change ((f ∘ i.1) ∘ i.2.1 ≈ f).
    rewrite comp_assoc, (snd i.2.2), comp_id_r. reflexivity.
  - intros k Hk. destruct (fst HF _ _ k) as [a Ha].
    assert (K : a ≈ h).
    { apply Hu. apply (snd HF).
      apply (iso_cancel_r (iso_symm i)).
      change (fmap F (ev ∘ (a × id)) ∘ preserved_product_inv F HP Z X ≈
        fmap F g ∘ preserved_product_inv F HP Z X).
      rewrite <- exponential_image_uncurry, Ha, Hk, Hg.
      change (f ≈ (f ∘ i.1) ∘ i.2.1).
      rewrite comp_assoc, (snd i.2.2), comp_id_r. reflexivity. }
    rewrite <- Ha, K. reflexivity.
Defined.

End ExponentialImages.

(** A universal exponential transpose on specified object representatives
    extends to all objects by composing with their chosen isomorphisms. *)

(** 指定对象代表上的泛指数转置通过与选定同构复合推广到全部对象。 *)

Definition exponential_from_representatives {D : Cat} {I : Type}
    (R : I → @Ob D) (HS : ∀ Z : @Ob D, ∃ i : I, R i ≅ Z)
    `{PD : !HasProduct D} {X Y E : @Ob D} (ev : Hom (E × X) Y)
    (HE : ∀ i (f : Hom (R i × X) Y), ∃ h : Hom (R i) E,
      is_unique (λ h, ev ∘ (h × id) ≈ f) h)
  : is_exponential X Y E ev.
Proof.
  intros Z f. destruct (HS Z) as [W i].
  destruct (HE W (f ∘ (i.1 × id))) as [h [Hh Hu]].
  exists (h ∘ i.2.1). refine {|this := _
                            ; that := _
                            |}.
  - apply (iso_cancel_r (product_iso i (@iso_refl D X))).
    change ((ev ∘ ((h ∘ i.2.1) × id)) ∘ (i.1 × id) ≈ f ∘ (i.1 × id)).
    rewrite comp_assoc, <- cross_comp, comp_id_l, comp_assoc,
      (fst i.2.2), comp_id_r. exact Hh.
  - intros k Hk.
    apply (iso_cancel_r i).
    rewrite comp_assoc, (fst i.2.2), comp_id_r.
    apply Hu.
    rewrite <- (comp_id_l (@Cats.Cat.Core.id D X)) at 1.
    rewrite cross_comp, <- comp_assoc, Hk. reflexivity.
Defined.

(** A fully faithful, essentially surjective, product-preserving functor
    preserves every specified exponential candidate. *)

(** 全忠实、本质满且保持积的函子保持任意指定指数候选。 *)

Definition equivalence_preserves_exponential {C D : Cat}
    (F : Functor C D) (HF : is_fully_faithful F)
    (HS : is_essentially_surjective F)
    `{PC : !HasProduct C} `{PD : !HasProduct D}
    (HP : ∀ X Y, is_product (F X) (F Y) (F ((X × Y)%ob))
      (fmap F (@Cats.Cat.Product.Core.π1 C PC X Y))
      (fmap F (@Cats.Cat.Product.Core.π2 C PC X Y)))
    {X Y E : @Ob C} (ev : Hom (E × X) Y)
    (HE : is_exponential X Y E ev)
  : is_exponential (F X) (F Y) (F E) (exponential_image_eval F HP ev)
  := exponential_from_representatives F HS (exponential_image_eval F HP ev)
      (fully_faithful_exponential_at_image F HP HF ev HE).
