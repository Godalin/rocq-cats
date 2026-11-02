From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Diagram.

(** * Changing the Shape of a Cone *)

Program Definition RestrictCone {I J C : Cat} (Q : Functor I J)
    {D : Functor J C} {X} (κ : X ⇒Δ D) : X ⇒Δ (D ∘F Q) :=
  {| nt i := κ (Q i) |}.
Next Obligation.
  rewrite comp_id_r. apply cone_naturality.
Qed.

Notation "κ '∘Δ' Q" := (RestrictCone Q κ)
  (at level 40, left associativity) : cat_scope.

Global Instance cone_restrict_proper {I J C : Cat} (Q : Functor I J)
    {D : Functor J C} {X}
  : Proper (NatEq ==> NatEq) (@RestrictCone I J C Q D X).
Proof. intros κ μ H i. exact (H (Q i)). Qed.

Lemma cone_restrict_comp {I J C : Cat} (Q : Functor I J)
    {D : Functor J C} {X Y} (κ : X ⇒Δ D) (f : Hom Y X)
  : (κ ∘Cone f) ∘Δ Q ≈N (κ ∘Δ Q) ∘Cone f.
Proof. intros i. reflexivity. Qed.

(** Essential surjectivity alone detects equality of cones. Fullness will be
    needed to extend arbitrary cones on the restricted diagram. *)
Lemma cone_restrict_reflects {I J C : Cat} {Q : Functor I J}
    (HQ : is_essentially_surjective Q) {D : Functor J C} {X}
    (κ μ : X ⇒Δ D)
  : κ ∘Δ Q ≈N μ ∘Δ Q → κ ≈N μ.
Proof.
  intros H j. destruct (HQ j) as [i e].
  rewrite (cone_naturality κ e.1), (cone_naturality μ e.1).
  apply comp_l. exact (H i).
Qed.

Section ConeExtension.
Context {I J C : Cat} {Q : Functor I J}.
Context (HF : is_full Q) (HQ : is_essentially_surjective Q).
Context {D : Functor J C}.

Definition cone_extend_leg {X} (κ : X ⇒Δ (D ∘F Q)) (j : @Ob J)
  : Hom X (D j) :=
  fmap D (HQ j).2.1 ∘ κ (HQ j).1.

(** Any arrow to [j] gives the same extended leg. Its preimage is used only
    in the proof; the computed leg uses the chosen object isomorphism. *)
Lemma cone_extend_leg_comm {X} (κ : X ⇒Δ (D ∘F Q))
    {i : @Ob I} {j : @Ob J} (f : Hom (Q i) j)
  : fmap D f ∘ κ i ≈ cone_extend_leg κ j.
Proof.
  destruct (HF i (HQ j).1 ((HQ j).2.2.1 ∘ f)) as [g Hg].
  unfold cone_extend_leg. symmetry.
  rewrite (cone_naturality κ g).
  change (fmap D (HQ j).2.1 ∘ (fmap D (fmap Q g) ∘ κ i) ≈
    fmap D f ∘ κ i).
  rewrite <- comp_assoc, <- functor_comp.
  apply comp_r. apply functor_fmap_proper.
  rewrite Hg, <- comp_assoc, (snd (HQ j).2.2.2), comp_id_l.
  reflexivity.
Qed.

Program Definition ExtendCone {X} (κ : X ⇒Δ (D ∘F Q)) : X ⇒Δ D :=
  {| nt j := cone_extend_leg κ j |}.
Next Obligation.
  rewrite comp_id_r. unfold cone_extend_leg at 2.
  rewrite <- comp_assoc, <- functor_comp.
  symmetry. apply cone_extend_leg_comm.
Qed.

Global Instance cone_extend_proper {X}
  : Proper (NatEq ==> NatEq) (@ExtendCone X).
Proof.
  intros κ μ H j. cbn. unfold cone_extend_leg.
  apply comp_l. apply H.
Qed.

Lemma cone_extend_comp {X Y} (κ : X ⇒Δ (D ∘F Q)) (f : Hom Y X)
  : ExtendCone (κ ∘Cone f) ≈N ExtendCone κ ∘Cone f.
Proof. intros j. symmetry. apply comp_assoc. Qed.

Lemma cone_extend_restrict {X} (κ : X ⇒Δ D)
  : ExtendCone (κ ∘Δ Q) ≈N κ.
Proof. intros j. symmetry. apply (cone_naturality κ (HQ j).2.1). Qed.

Lemma cone_restrict_extend {X} (κ : X ⇒Δ (D ∘F Q))
  : ExtendCone κ ∘Δ Q ≈N κ.
Proof.
  intros i. symmetry.
  transitivity (fmap D (@id (Q i)) ∘ κ i).
  - rewrite functor_id, comp_id_l. reflexivity.
  - apply cone_extend_leg_comm.
Qed.

End ConeExtension.

