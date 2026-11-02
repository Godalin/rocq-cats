From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Arrow Cat.Equalizer.
From Cats Require Export Cat.Product.Indexed.

(** * Constructing Limits from Products and Equalizers

    Only two particular products are needed: one over the objects and one
    over the arrows of the index category. Their size bounds remain explicit
    in the chosen product assumptions. *)
Definition DiagramObjects {J C : Cat} (D : Functor J C) (j : @Ob J) : @Ob C := D j.
Definition DiagramTargets {J C : Cat} (D : Functor J C) (a : ArrowOb J) : @Ob C :=
  D (arrow_cod a).

Section ProductsEqualizer.
Context {J C : Cat} (D : Functor J C).
Context `{HO : !HasLimit C (DiscreteF (DiagramObjects D))}.
Context `{HA : !HasLimit C (DiscreteF (DiagramTargets D))}.

Definition diagram_product_source : Hom Π[DiagramObjects D] Π[DiagramTargets D] :=
  Π⟨λ a, fmap D (arrow_map a) ∘ πΠ[DiagramObjects D] (arrow_dom a)⟩.

Definition diagram_product_target : Hom Π[DiagramObjects D] Π[DiagramTargets D] :=
  Π⟨λ a, πΠ[DiagramObjects D] (arrow_cod a)⟩.

Lemma diagram_product_comm {E : @Ob C} (e : Hom E Π[DiagramObjects D])
    (H : diagram_product_source ∘ e ≈ diagram_product_target ∘ e)
    {i j : @Ob J} (f : Hom i j)
  : fmap D f ∘ (πΠ[DiagramObjects D] i ∘ e) ≈ πΠ[DiagramObjects D] j ∘ e.
Proof.
  pose (a := ({| arrow_dom := i; arrow_cod := j; arrow_map := f |} : ArrowOb J)).
  transitivity ((πΠ[DiagramTargets D] a ∘ diagram_product_source) ∘ e).
  - unfold diagram_product_source. rewrite indexed_product_β, comp_assoc. reflexivity.
  - rewrite comp_assoc, H, <- comp_assoc.
    unfold diagram_product_target. rewrite indexed_product_β. reflexivity.
Qed.

Program Definition ProductsEqualizerCone {E : @Ob C} (e : Hom E Π[DiagramObjects D])
    (H : diagram_product_source ∘ e ≈ diagram_product_target ∘ e) : E ⇒Δ D :=
  {| nt j := πΠ[DiagramObjects D] j ∘ e |}.
Next Obligation.
  rewrite comp_id_r. symmetry. apply diagram_product_comm. exact H.
Qed.

Definition products_equalizer_limit {E : @Ob C} {e : Hom E Π[DiagramObjects D]}
    (H : diagram_product_source ∘ e ≈ diagram_product_target ∘ e)
    (HE : is_equalizer diagram_product_source diagram_product_target E e)
  : is_limit (ProductsEqualizerCone e H).
Proof.
  intros X μ.
  pose (p := indexed_pair (D := DiagramObjects D) (λ j, μ j)).
  assert (Hp : diagram_product_source ∘ p ≈ diagram_product_target ∘ p).
  { apply indexed_product_hom_ext. intros a.
    unfold diagram_product_source, diagram_product_target.
    rewrite <- !comp_assoc, !indexed_product_β, comp_assoc.
    unfold p. rewrite !indexed_product_β.
    pose proof (nt_naturality μ (arrow_map a)) as Hμ.
    cbn in Hμ. rewrite comp_id_r in Hμ.
    transitivity (μ (arrow_cod a)).
    - symmetry. exact Hμ.
    - symmetry. apply (indexed_product_β (D := DiagramObjects D)). }
  destruct (snd HE X p Hp) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - intros j.
    change ((πΠ[DiagramObjects D] j ∘ e) ∘ h ≈ μ j).
    rewrite comp_assoc, (@this _ _ _ _ _ Hh).
    unfold p. apply (indexed_product_β (D := DiagramObjects D)).
  - intros k Hk. apply (@that _ _ _ _ _ Hh).
    apply indexed_product_hom_ext. intros j.
    rewrite <- comp_assoc. transitivity (μ j).
    + exact (Hk j).
    + unfold p. symmetry. apply (indexed_product_β (D := DiagramObjects D)).
Defined.

Program Definition ProductsEqualizerLimit `{HE : !HasEqualizer C} : HasLimit C D :=
  {| Lim := Eq[diagram_product_source, diagram_product_target]
   ; limit_cone := ProductsEqualizerCone
       ιeq[diagram_product_source, diagram_product_target] equalizer_comm |}.
Next Obligation. apply products_equalizer_limit. exact equalizer_universal. Defined.

End ProductsEqualizer.

(** Uniform product choices give all limits of the shape. No new choice
    of maps or functoriality laws is needed for the resulting limit functor. *)
Program Definition IndexedProductsEqualizerLimits {J C : Cat}
    `{HO : !HasLimitsOfShape C (DiscreteCat (@Ob J))}
    `{HA : !HasLimitsOfShape C (DiscreteCat (ArrowOb J))}
    `{HE : !HasEqualizer C} : HasLimitsOfShape C J :=
  {| hasLimit D := ProductsEqualizerLimit D |}.
