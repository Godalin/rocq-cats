From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core.
From Cats Require Import
  Cat.Diagram.Reindex
  Cat.Limit.Core.

(** * Limits along Full, Essentially Surjective Functors *)

(** * 沿满且本质满函子传递极限 *)

(** Detecting a limiting cone requires only essential surjectivity. *)

(** 检测极限锥只需本质满。 *)

Definition limit_of_restrict {I J C : Cat} {Q : Fct I J}
    (HQ : is_essentially_surjective Q) {D : Fct J C} {L}
    {κ : L ⇒Δ D} (Hκ : is_limit (κ ∘Δ Q))
  : is_limit κ.
Proof.
  intros X μ. destruct (Hκ X (μ ∘Δ Q)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - apply (cone_restrict_reflects HQ).
    exact (@this _ _ _ _ _ Hh).
  - intros g Hg. apply Hh. intros i. exact (Hg (Q i)).
Defined.

(** Fullness extends every source cone. Neither faithfulness nor equality of
    object representatives is required. *)

(** 满性保证每个源形状上的锥都能延拓；不需要忠实性或对象代表的原生相等。 *)

Definition restrict_limit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Fct J C} {L} {κ : L ⇒Δ D} (Hκ : is_limit κ)
  : is_limit (κ ∘Δ Q).
Proof.
  intros X μ. destruct (Hκ X (ExtendCone HF HQ μ)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - transitivity (ExtendCone HF HQ μ ∘Δ Q).
    + intros i. exact (@this _ _ _ _ _ Hh (Q i)).
    + apply cone_restrict_extend.
  - intros g Hg. apply Hh. apply (cone_restrict_reflects HQ).
    transitivity μ; [exact Hg | symmetry; apply cone_restrict_extend].
Defined.

(** Full, essentially surjective restriction preserves and reflects limiting
    cones. *)

(** 满且本质满的形状限制保持并反映极限锥。 *)

Theorem limit_iff_restrict {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Fct J C} {L} (κ : L ⇒Δ D)
  : is_limit κ ↔ is_limit (κ ∘Δ Q).
Proof. split; [apply (restrict_limit HF HQ) | apply (limit_of_restrict HQ)]. Defined.

(** Extend a limit of the composite diagram to a limit of the original
    diagram. *)

(** 将复合图式的极限延拓为原图式的极限。 *)

Definition extend_limit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Fct J C} {L} {κ : L ⇒Δ (D ∘F Q)} (Hκ : is_limit κ)
  : is_limit (ExtendCone HF HQ κ).
Proof.
  apply (limit_of_restrict HQ).
  intros X μ. destruct (Hκ X μ) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros i. change (ExtendCone HF HQ κ (Q i) ∘ h ≈ μ i).
    rewrite (cone_restrict_extend HF HQ κ i).
    exact (@this _ _ _ _ _ Hh i).
  - intros g Hg. apply Hh. intros i.
    change (κ i ∘ g ≈ μ i).
    rewrite <- (cone_restrict_extend HF HQ κ i). exact (Hg i).
Defined.

(** Select a target-shape limit by extending the chosen source-shape limit
    cone. *)

(** 通过延拓选定源形状极限锥，选择目标形状的极限。 *)

Program Definition ReindexedLimit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    (D : Fct J C) `{HL : !HasLimit C (D ∘F Q)}
  : HasLimit C D
  :=
  {|Lim := lim (D ∘F Q)
  ; limit_cone := ExtendCone HF HQ πlim[D ∘F Q]
  |}.
Next Obligation. apply extend_limit. apply limit_universal. Defined.

(** Restrict a selected limit in the other direction, keeping its apex and
    using the original restriction theorem for its universal property. *)

(** 反向限制选定极限，保留顶点，并用原限制定理给出泛性质。 *)

Program Definition RestrictedLimit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    (D : Fct J C) `{HL : !HasLimit C D}
  : HasLimit C (D ∘F Q)
  :=
  {|Lim := lim D
  ; limit_cone := πlim[D] ∘Δ Q
  |}.
Next Obligation. apply (restrict_limit HF HQ). apply limit_universal. Defined.

(** Transfer selected limits of a whole shape along a full, essentially
    surjective functor. *)

(** 沿满且本质满函子传递整个形状的选定极限。 *)

Program Definition ReindexedLimits {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    `{HL : !HasLimitsOfShape C I}
  : HasLimitsOfShape C J
  :=
  {|hasLimit D := ReindexedLimit HF HQ D
  |}.

