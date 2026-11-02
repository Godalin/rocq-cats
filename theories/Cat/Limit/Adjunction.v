From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Adjunction.
From Cats Require Import Cat.Diagram Cat.Limit.

(** * Limits as Right Adjoints to the Diagonal

    Functoriality of the selected limits is derived from their universal
    properties. No separate coherence choices for limit maps are stored. *)
Section ChosenLimits.
Context {J C : Cat} `{HL : !HasLimitsOfShape C J}.

Program Definition limit_lift_resp {X : @Ob C} {D : Functor J C}
  : @HomSet (Fct J C) (ConstF J X) D →r HomSet X (lim D) :=
  {| func := limit_lift |}.

Program Definition limit_cone_resp {X : @Ob C} {D : Functor J C}
  : HomSet X (lim D) →r @HomSet (Fct J C) (ConstF J X) D :=
  {| func f := πlim[D] ∘Cone f |}.
Next Obligation. intros f g H j. cbn. rewrite H. reflexivity. Defined.

Definition LimitAdjunction : Δ[J,C] ⊣ LimitF.
Proof.
  refine (AdjunctionFromHom Δ[J,C] LimitF
    (λ X D, limit_lift_resp) (λ X D, limit_cone_resp) _ _ _ _).
  - intros X D κ. apply limit_β.
  - intros X D f. apply limit_η.
  - intros X Y D κ f.
    change (lim⟨ κ ∘Cone f ⟩ ≈ lim⟨ κ ⟩ ∘ f). apply limit_lift_comp.
  - intros X D E α κ.
    change (lim⟨ α ∘Nv κ ⟩ ≈ limit_map α ∘ lim⟨ κ ⟩). apply limit_lift_map.
Defined.

End ChosenLimits.

(** Conversely, the counit of a diagonal adjunction supplies limiting cones.
    This constructs chosen limits explicitly; it is not a global instance. *)
Section DiagonalAdjunction.
Context {J C : Cat} {R : Functor (Fct J C) C} (A : Δ[J,C] ⊣ R).

Program Definition DiagonalAdjunctionLimit (D : Functor J C) : HasLimit C D :=
  {| Lim := R D
   ; limit_cone := adjunction_counit A D |}.
Next Obligation.
  intros X κ. exists (κ^♯[A]). refine {| this := _; that := _ |}.
  - intros j.
    exact (transitivity (symmetry (unadjunct_counit A (κ^♯[A]) j))
      (adjunction_β A κ j)).
  - intros f H. symmetry. apply (snd (adjunct_iff A κ f)).
    transitivity (adjunction_counit A D ∘Nv fmap Δ[J,C] f).
    + symmetry. exact H.
    + exact (symmetry (unadjunct_counit A f)).
Defined.

Program Definition DiagonalAdjunctionLimits : HasLimitsOfShape C J :=
  {| hasLimit := DiagonalAdjunctionLimit |}.

End DiagonalAdjunction.

Theorem limits_iff_diagonal_right_adjoint (J C : Cat)
  : HasLimitsOfShape C J ↔ ∃ R : Functor (Fct J C) C, Δ[J,C] ⊣ R.
Proof.
  split.
  - intros HL. exists (@LimitF J C HL). exact (@LimitAdjunction J C HL).
  - intros [R A]. exact (DiagonalAdjunctionLimits A).
Defined.
