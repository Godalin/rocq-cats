From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Adjunction.
From Cats Require Import Cat.Diagram Cat.Limit.

(** * Right Adjoints Preserve Limits

    Cone legs transpose componentwise. Their naturality is inherited from
    the natural hom isomorphism, without any new chosen coherence data. *)
Section RightAdjointLimits.
Context {C D J : Cat} {F : Functor C D} {G : Functor D C} (A : F ⊣ G).

Program Definition UnadjunctCone {K : Functor J D} {X : @Ob C}
    (κ : X ⇒Δ (G ∘F K)) : F X ⇒Δ K :=
  {| nt j := (κ j)^♭[A] |}.
Next Obligation.
  rewrite comp_id_r, <- (unadjunct_comp_l A (fmap K f) (κ X0)).
  apply (unadjunct_proper A).
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_r in H. exact H.
Qed.

Definition right_adjoint_preserves_limit {K : Functor J D} {L : @Ob D}
    {κ : L ⇒Δ K} (Hκ : is_limit κ) : is_limit (MapCone G κ).
Proof.
  intros X μ. destruct (Hκ (F X) (UnadjunctCone μ)) as [f Hf].
  exists (f^♯[A]). refine {| this := _; that := _ |}.
  - intros j.
    change (fmap G (κ j) ∘ f^♯[A] ≈ μ j).
    transitivity ((κ j ∘ f)^♯[A]).
    + symmetry. apply adjunct_comp_l.
    + transitivity (((μ j)^♭[A])^♯[A]).
      * apply (adjunct_proper A). exact (@this _ _ _ _ _ Hf j).
      * apply adjunction_η.
  - intros g Hg.
    transitivity ((g^♭[A])^♯[A]).
    + symmetry. apply adjunction_η.
    + apply (adjunct_proper A). apply (@that _ _ _ _ _ Hf). intros j.
      change (κ j ∘ g^♭[A] ≈ (μ j)^♭[A]).
      transitivity ((fmap G (κ j) ∘ g)^♭[A]).
      * symmetry. apply unadjunct_comp_l.
      * apply (unadjunct_proper A). exact (Hg j).
Defined.

End RightAdjointLimits.
