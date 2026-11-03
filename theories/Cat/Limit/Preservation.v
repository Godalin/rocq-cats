From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Adjunction.
From Cats Require Import
  Cat.Diagram.Core
  Cat.Limit.Core.

(** * Right Adjoints Preserve Limits

    Cone legs transpose componentwise. Their naturality is inherited from the
    natural hom isomorphism, without any new chosen coherence data. *)

(** * 右伴随保持极限

    各锥腿逐分量转置；自然性来自自然 Hom 同构，不增加新的相干选择。 *)

Section RightAdjointLimits.
Context {C D J : Cat} {F : Functor C D} {G : Functor D C} (A : F ⊣ G).

(** Transpose cone legs inversely along a hom adjunction. *)

(** 沿 Hom 伴随逆向转置每条锥腿。 *)

Program Definition UnadjunctCone {K : Functor J D} {X : @Ob C}
    (κ : X ⇒Δ (G ∘F K))
  : F X ⇒Δ K
  :=
  {|nt j := (κ j)^♭[A]
  |}.
Next Obligation.
  rewrite comp_id_r, <- (unadjunct_comp_l A (fmap K f) (κ X0)).
  apply (unadjunct_proper A).
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_r in H. exact H.
Qed.

(** A right adjoint sends a limiting cone to a limiting cone. *)

(** 右伴随将极限锥送到极限锥。 *)

Definition right_adjoint_preserves_limit {K : Functor J D} {L : @Ob D}
    {κ : L ⇒Δ K} (Hκ : is_limit κ)
  : is_limit (MapCone G κ).
Proof.
  intros X μ. destruct (Hκ (F X) (UnadjunctCone μ)) as [f Hf].
  exists (f^♯[A]). refine {|this := _
                          ; that := _
                          |}.
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
