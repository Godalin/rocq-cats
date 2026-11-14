From Cats Require Import
  Cat.Core
  Cat.Equalizer.
From Cats Require Export
  Cat.Product.Indexed.

(** * Families Factoring through a Product Equalizer *)

(** * 经过积的等化子分解的箭头族 *)

(** A family determines a map to its chosen product. If that map equalizes
    two constraints, it factors uniquely through their candidate equalizer.
    This argument applies to cones and wedges without storing either one. *)

(** 箭头族确定指向选定积的映射。若该映射等化两条约束，就经过其候选等化子唯一
    分解。此论证适用于锥和楔，而不存储其中任何一种结构。 *)

Definition indexed_product_equalizer_universal {C : Cat} {I : Type}
    (D : I → @Ob C) `{HP : !HasLimit C (DiscreteF D)}
    {Q E : @Ob C} {s t : Hom ∏[D] Q} {e : Hom E ∏[D]}
    (HE : is_equalizer s t E e) (X : @Ob C)
    (μ : ∀ i, Hom X (D i))
    (Hμ : s ∘ ∏⟨μ⟩ ≈ t ∘ ∏⟨μ⟩)
  : ∃ h : Hom X E,
      is_unique (λ h, ∀ i, (π∏[D] i ∘ e) ∘ h ≈ μ i) h.
Proof.
  destruct (snd HE X ∏⟨μ⟩ Hμ) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros i. rewrite comp_assoc, (@this _ _ _ _ _ Hh).
    apply indexed_product_β.
  - intros k Hk. apply (@that _ _ _ _ _ Hh).
    apply indexed_product_hom_ext. intros i.
    rewrite <- comp_assoc. transitivity (μ i).
    + exact (Hk i).
    + symmetry. apply indexed_product_β.
Defined.
