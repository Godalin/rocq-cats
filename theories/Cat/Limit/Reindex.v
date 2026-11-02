From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Diagram.
From Cats Require Import
  Cat.Diagram.Reindex
  Cat.Limit.

(** * Limits along Full, Essentially Surjective Functors *)

(** Detecting a limiting cone requires only essential surjectivity. *)
Definition limit_of_restrict {I J C : Cat} {Q : Functor I J}
    (HQ : is_essentially_surjective Q) {D : Functor J C} {L}
    {κ : L ⇒Δ D} (Hκ : is_limit (κ ∘Δ Q))
  : is_limit κ.
Proof.
  intros X μ. destruct (Hκ X (μ ∘Δ Q)) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - apply (cone_restrict_reflects HQ).
    exact (@this _ _ _ _ _ Hh).
  - intros g Hg. apply Hh. intros i. exact (Hg (Q i)).
Defined.

(** Fullness extends every source cone. Neither faithfulness nor equality of
    object representatives is required. *)
Definition restrict_limit {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Functor J C} {L} {κ : L ⇒Δ D} (Hκ : is_limit κ)
  : is_limit (κ ∘Δ Q).
Proof.
  intros X μ. destruct (Hκ X (ExtendCone HF HQ μ)) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - transitivity (ExtendCone HF HQ μ ∘Δ Q).
    + intros i. exact (@this _ _ _ _ _ Hh (Q i)).
    + apply cone_restrict_extend.
  - intros g Hg. apply Hh. apply (cone_restrict_reflects HQ).
    transitivity μ; [exact Hg | symmetry; apply cone_restrict_extend].
Defined.

Theorem limit_iff_restrict {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Functor J C} {L} (κ : L ⇒Δ D)
  : is_limit κ ↔ is_limit (κ ∘Δ Q).
Proof. split; [apply (restrict_limit HF HQ) | apply (limit_of_restrict HQ)]. Defined.

Definition extend_limit {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Functor J C} {L} {κ : L ⇒Δ (D ∘F Q)} (Hκ : is_limit κ)
  : is_limit (ExtendCone HF HQ κ).
Proof.
  apply (limit_of_restrict HQ).
  intros X μ. destruct (Hκ X μ) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - intros i. change (ExtendCone HF HQ κ (Q i) ∘ h ≈ μ i).
    rewrite (cone_restrict_extend HF HQ κ i).
    exact (@this _ _ _ _ _ Hh i).
  - intros g Hg. apply Hh. intros i.
    change (κ i ∘ g ≈ μ i).
    rewrite <- (cone_restrict_extend HF HQ κ i). exact (Hg i).
Defined.

Program Definition ReindexedLimit {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    (D : Functor J C) `{HL : !HasLimit C (D ∘F Q)}
  : HasLimit C D
  := {| Lim := lim (D ∘F Q)
      ; limit_cone := ExtendCone HF HQ πlim[D ∘F Q] |}.
Next Obligation. apply extend_limit. apply limit_universal. Defined.

Program Definition ReindexedLimits {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    `{HL : !HasLimitsOfShape C I}
  : HasLimitsOfShape C J
  := {| hasLimit D := ReindexedLimit HF HQ D |}.

