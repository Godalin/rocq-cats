From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Diagram Cat.Terminal.

(** * Limits of Diagrams

    The candidate property retains a unique mediator for every cone.
    Chosen limits are separate, as for products and pullbacks. *)
Definition is_limit {J C : Cat} {D : Functor J C} {L : @Ob C} (κ : L ⇒Δ D) :=
  ∀ X (μ : X ⇒Δ D), ∃ h : Hom X L, is_unique (λ h, κ ∘Cone h ≈N μ) h.

Notation "κ '⦂' 'Lim(' D ')'" := (@is_limit _ _ D _ κ)
  (at level 50, no associativity) : cat_scope.

Class HasLimit (C : Cat) {J : Cat} (D : Functor J C) :=
  { Lim : @Ob C
  ; limit_cone : Lim ⇒Δ D
  ; limit_universal : is_limit limit_cone }.

Arguments Lim {_ _} _ {_}.
Arguments limit_cone {_ _} _ {_}.
Arguments limit_universal {_ _} _ {_} _ _.
Notation "'lim' D" := (Lim D) (at level 35) : ob_scope.
Notation "'πlim[' D ']'" := (limit_cone D) : hom_scope.

Section ChosenLimit.
Context {J C : Cat} {D : Functor J C} `{HL : !HasLimit C D}.

Definition limit_lift {X} (κ : X ⇒Δ D) : Hom X (lim D) :=
  (limit_universal D X κ).1.

Theorem limit_lift_unique {X} (κ : X ⇒Δ D)
  : is_unique (λ h, πlim[D] ∘Cone h ≈N κ) (limit_lift κ).
Proof. exact (limit_universal D X κ).2. Defined.

Theorem limit_β {X} (κ : X ⇒Δ D)
  : πlim[D] ∘Cone limit_lift κ ≈N κ.
Proof. exact (@this _ _ _ _ _ (limit_lift_unique κ)). Qed.

Theorem limit_η {X} (f : Hom X (lim D))
  : limit_lift (πlim[D] ∘Cone f) ≈ f.
Proof. symmetry. apply limit_lift_unique. reflexivity. Qed.

Global Instance limit_lift_proper {X}
  : Proper (NatEq ==> @HomEq[X, lim D]) (@limit_lift X).
Proof.
  intros κ μ H. apply limit_lift_unique. rewrite limit_β. exact H.
Qed.

Lemma limit_lift_comp {X Y} (κ : X ⇒Δ D) (f : Hom Y X)
  : limit_lift (κ ∘Cone f) ≈ limit_lift κ ∘ f.
Proof.
  symmetry. apply limit_lift_unique.
  rewrite <- cone_comp_assoc, limit_β. reflexivity.
Qed.

End ChosenLimit.

Notation "'lim⟨' κ '⟩'" := (limit_lift κ) (at level 35) : hom_scope.

(** A limiting cone is exactly a terminal object of the cone category.
    Consequently object uniqueness reuses the general terminal-object theorem. *)
Definition limit_terminal {J C : Cat} {D : Functor J C} {L : @Ob C}
    {κ : L ⇒Δ D} (Hκ : is_limit κ) : @is_terminal (ConeCat D) (L; κ).
Proof.
  intros [X μ]. destruct (Hκ X μ) as [f Hf].
  exists (f; @this _ _ _ _ _ Hf).
  refine {| this := I; that := _ |}. intros [g Hg] _.
  exact (@that _ _ _ _ _ Hf g Hg).
Defined.

Definition terminal_limit {J C : Cat} {D : Functor J C} {L : @Ob C}
    {κ : L ⇒Δ D} (Hκ : @is_terminal (ConeCat D) (L; κ)) : is_limit κ.
Proof.
  intros X μ. destruct (Hκ (X; μ)) as [f Hf].
  exists f.1. refine {| this := f.2; that := _ |}.
  intros g Hg. exact (@that _ _ _ _ _ Hf (g; Hg) I).
Defined.

Theorem limit_iff_terminal {J C : Cat} {D : Functor J C} {L : @Ob C}
    (κ : L ⇒Δ D) : is_limit κ ↔ @is_terminal (ConeCat D) (L; κ).
Proof. split; [apply limit_terminal | apply terminal_limit]. Defined.

Definition limit_unique {J C : Cat} {D : Functor J C} {L M : @Ob C}
    {κ : L ⇒Δ D} {μ : M ⇒Δ D} (Hκ : is_limit κ) (Hμ : is_limit μ)
  : L ≅[C] M.
Proof.
  pose (i := terminal_unique (limit_terminal Hκ) (limit_terminal Hμ)).
  exists (fmap (ConeApexF D) i.1).
  exact (functor_is_iso (ConeApexF D) i.1 i.2).
Defined.

Class HasLimitsOfShape (C J : Cat) :=
  { hasLimit (D : Functor J C) :: HasLimit C D }.

Section LimitFunctor.
Context {J C : Cat} `{HL : !HasLimitsOfShape C J}.

Definition limit_map {D E : Functor J C} (α : D => E) : Hom (lim D) (lim E) :=
  lim⟨ α ∘Nv πlim[D] ⟩.

Lemma limit_map_comm {D E : Functor J C} (α : D => E)
  : πlim[E] ∘Cone limit_map α ≈N (α ∘Nv πlim[D]).
Proof. apply limit_β. Qed.

Lemma limit_map_β {D E : Functor J C} (α : D => E) (j : @Ob J)
  : πlim[E] j ∘ limit_map α ≈ α j ∘ πlim[D] j.
Proof. exact (limit_map_comm α j). Qed.

Global Instance limit_map_proper {D E : Functor J C}
  : Proper (NatEq ==> @HomEq[lim D, lim E]) (@limit_map D E).
Proof.
  intros α β H. apply limit_lift_proper. intros j. cbn. rewrite (H j). reflexivity.
Qed.

Lemma limit_map_id {D : Functor J C} : limit_map (idN (F := D)) ≈ id.
Proof.
  unfold limit_map. rewrite <- (limit_η (@id (lim D))).
  apply limit_lift_proper. intros j. cbn. carw.
Qed.

Lemma limit_map_comp {D E K : Functor J C} (β : E => K) (α : D => E)
  : limit_map (β ∘Nv α) ≈ limit_map β ∘ limit_map α.
Proof.
  symmetry. apply limit_lift_unique. intros j.
  change (πlim[K] j ∘ (limit_map β ∘ limit_map α) ≈
    (β j ∘ α j) ∘ πlim[D] j).
  rewrite <- (comp_assoc (πlim[K] j) (limit_map β) (limit_map α)),
    (limit_map_β β j), (comp_assoc (β j) (πlim[E] j) (limit_map α)),
    (limit_map_β α j).
  symmetry. apply comp_assoc.
Qed.

Program Definition LimitF : Functor (Fct J C) C :=
  {| F0 D := lim D; F1 D E α := limit_map α |}.
Next Obligation. apply limit_map_id. Qed.
Next Obligation. apply limit_map_comp. Qed.

Lemma limit_lift_map {D E : Functor J C} (α : D => E) {X} (κ : X ⇒Δ D)
  : lim⟨ α ∘Nv κ ⟩ ≈ limit_map α ∘ lim⟨ κ ⟩.
Proof.
  symmetry. apply limit_lift_unique. intros j.
  change (πlim[E] j ∘ (limit_map α ∘ lim⟨ κ ⟩) ≈ α j ∘ κ j).
  rewrite <- (comp_assoc (πlim[E] j) (limit_map α) (lim⟨ κ ⟩)),
    (limit_map_β α j).
  transitivity (α j ∘ (πlim[D] j ∘ lim⟨ κ ⟩)).
  - apply comp_assoc.
  - apply comp_l. exact (limit_β κ j).
Qed.

End LimitFunctor.
