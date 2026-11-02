From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Equalizer.
From Cats Require Export Cat.Limit.Construction Cat.Diagram.Free.

(** * Limits Specified by Graph Generators

    Products are indexed by vertices and generators, not by all paths. *)
Definition GraphTargets {G : Graph} {C : Cat} (D : Functor (FreeCat G) C)
    (a : GraphEdges G) : @Ob C := D a.2.1.

Section GraphLimits.
Context {G : Graph} {C : Cat} (D : Functor (FreeCat G) C).
Context `{HO : !HasLimit C (DiscreteF (DiagramObjects D))}.
Context `{HG : !HasLimit C (DiscreteF (GraphTargets D))}.

Definition graph_product_source : Hom Π[DiagramObjects D] Π[GraphTargets D] :=
  Π⟨λ a, fmap D (ιG a.2.2) ∘ πΠ[DiagramObjects D] a.1⟩.

Definition graph_product_target : Hom Π[DiagramObjects D] Π[GraphTargets D] :=
  Π⟨λ a, πΠ[DiagramObjects D] a.2.1⟩.

Lemma graph_product_comm {E : @Ob C} (e : Hom E Π[DiagramObjects D])
    (H : graph_product_source ∘ e ≈ graph_product_target ∘ e)
    {x y : @Vertex G} (f : Edge x y)
  : fmap D (ιG f) ∘ (πΠ[DiagramObjects D] x ∘ e) ≈ πΠ[DiagramObjects D] y ∘ e.
Proof.
  pose (a := ((x; (y; f)) : GraphEdges G)).
  transitivity ((πΠ[GraphTargets D] a ∘ graph_product_source) ∘ e).
  - unfold graph_product_source. rewrite indexed_product_β, comp_assoc. reflexivity.
  - rewrite comp_assoc, H, <- comp_assoc.
    unfold graph_product_target. rewrite indexed_product_β. reflexivity.
Qed.

Definition GraphEqualizerCone {E : @Ob C} (e : Hom E Π[DiagramObjects D])
    (H : graph_product_source ∘ e ≈ graph_product_target ∘ e) : E ⇒Δ D :=
  @FreeCone G C D E (λ x, πΠ[DiagramObjects D] x ∘ e)
    (λ x y f, graph_product_comm e H f).

Definition graph_products_equalizer_limit {E : @Ob C} {e : Hom E Π[DiagramObjects D]}
    (H : graph_product_source ∘ e ≈ graph_product_target ∘ e)
    (HE : is_equalizer graph_product_source graph_product_target E e)
  : is_limit (GraphEqualizerCone e H).
Proof.
  refine (product_cone_equalizer_limit D (GraphEqualizerCone e H) _ _ HE).
  - intros x. reflexivity.
  - intros X μ. apply indexed_product_hom_ext. intros [x [y f]].
    unfold graph_product_source, graph_product_target.
    rewrite <- !comp_assoc, !indexed_product_β, comp_assoc, !indexed_product_β.
    transitivity (μ y).
    + exact (free_cone_edge μ f).
    + symmetry. apply (indexed_product_β (D := DiagramObjects D)).
Defined.

Program Definition GraphProductsEqualizerLimit `{HE : !HasEqualizer C}
  : HasLimit C D :=
  {| Lim := Eq[graph_product_source, graph_product_target]
   ; limit_cone := GraphEqualizerCone
       ιeq[graph_product_source, graph_product_target] equalizer_comm |}.
Next Obligation. apply graph_products_equalizer_limit. exact equalizer_universal. Defined.

End GraphLimits.

Program Definition GraphProductsEqualizerLimits {G : Graph} {C : Cat}
    `{HO : !HasLimitsOfShape C (DiscreteCat (@Vertex G))}
    `{HG : !HasLimitsOfShape C (DiscreteCat (GraphEdges G))}
    `{HE : !HasEqualizer C} : HasLimitsOfShape C (FreeCat G) :=
  {| hasLimit D := GraphProductsEqualizerLimit D |}.
