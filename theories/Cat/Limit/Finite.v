From Cats Require Import Cat.Core Cat.Terminal Cat.Product Cat.Equalizer Cat.Pullback.

(** * Two Bases for Finite Limits

    Each candidate construction uses only the structures it needs.
    Chosen structures are explicit conversions, not global instances. *)

(** An equalizer inside a product gives a pullback. *)
Definition product_equalizer_pullback {C : Cat} `{HP : !HasProduct C}
    {X Y Z E : @Ob C} {f : Hom X Z} {g : Hom Y Z} {e : Hom E (X × Y)}
    (HE : is_equalizer (f ∘ π1) (g ∘ π2) E e)
  : is_pullback f g E (π1 ∘ e) (π2 ∘ e).
Proof.
  split.
  - rewrite <- !comp_assoc. exact (fst HE).
  - intros Q p q Hpq.
    assert (H : (f ∘ π1) ∘ ⟨p, q⟩ ≈ (g ∘ π2) ∘ ⟨p, q⟩).
    { rewrite !comp_assoc, product_β1, product_β2. exact Hpq. }
    destruct (snd HE Q ⟨p, q⟩ H) as [h Hh].
    exists h. refine {| this := _; that := _ |}.
    + split; rewrite comp_assoc, (@this _ _ _ _ _ Hh);
        [apply product_β1 | apply product_β2].
    + intros k [Hk1 Hk2]. apply (@that _ _ _ _ _ Hh).
      rewrite (product_η (e ∘ k)), <- !comp_assoc, Hk1, Hk2. reflexivity.
Defined.

Program Definition ProductEqualizerPullback {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasEqualizer C} : HasPullback C :=
  {| Pb X Y Z f g := Eq[f ∘ π1, g ∘ π2]
   ; pb1 X Y Z f g := π1 ∘ ιeq[f ∘ π1, g ∘ π2]
   ; pb2 X Y Z f g := π2 ∘ ιeq[f ∘ π1, g ∘ π2] |}.
Next Obligation. apply product_equalizer_pullback. exact equalizer_universal. Defined.

(** Products from pullbacks over the chosen terminal object. *)
Program Definition PullbackProduct {C : Cat}
    `{HT : !HasTerminal C} `{HPb : !HasPullback C} : HasProduct C :=
  {| Prod X Y := X ×[!, !] Y
   ; π1 X Y := pb1 ! !
   ; π2 X Y := pb2 ! ! |}.
Next Obligation. apply pullback_product. Defined.

(** Pull back the diagonal of Y along the pair of parallel arrows. *)
Definition pullback_equalizer {C : Cat} `{HP : !HasProduct C}
    {X Y E : @Ob C} {f g : Hom X Y} {e : Hom E X} {d : Hom E Y}
    (HPb : is_pullback ⟨f, g⟩ ⟨id, id⟩ E e d) : is_equalizer f g E e.
Proof.
  assert (Hf : f ∘ e ≈ d).
  { transitivity (π1 ∘ (⟨f, g⟩ ∘ e)).
    - rewrite <- comp_assoc, product_β1. reflexivity.
    - rewrite (fst HPb), <- comp_assoc, product_β1, comp_id_l. reflexivity. }
  assert (Hg : g ∘ e ≈ d).
  { transitivity (π2 ∘ (⟨f, g⟩ ∘ e)).
    - rewrite <- comp_assoc, product_β2. reflexivity.
    - rewrite (fst HPb), <- comp_assoc, product_β2, comp_id_l. reflexivity. }
  split.
  - rewrite Hf, Hg. reflexivity.
  - intros Q q Hq.
    assert (H : ⟨f, g⟩ ∘ q ≈ ⟨id, id⟩ ∘ (f ∘ q)).
    { rewrite !product_comp_r, !comp_id_l, Hq. reflexivity. }
    destruct (snd HPb Q q (f ∘ q) H) as [h Hh].
    exists h. refine {| this := _; that := _ |}.
    + exact (fst (@this _ _ _ _ _ Hh)).
    + intros k Hk. apply (@that _ _ _ _ _ Hh). split; [exact Hk |].
      rewrite <- Hf, comp_assoc, Hk. reflexivity.
Defined.

Program Definition ProductPullbackEqualizer {C : Cat}
    `{HP : !HasProduct C} `{HPb : !HasPullback C} : HasEqualizer C :=
  {| EqObj X Y f g := Pb ⟨f, g⟩ ⟨id, id⟩
   ; eqι X Y f g := pb1 ⟨f, g⟩ ⟨id, id⟩ |}.
Next Obligation. apply (pullback_equalizer (d := pb2 _ _)). exact pullback_universal. Defined.

(** No independent product structure is required when terminal objects and
    pullbacks are already selected. *)
Definition PullbackEqualizer {C : Cat}
    `{HT : !HasTerminal C} `{HPb : !HasPullback C} : HasEqualizer C :=
  @ProductPullbackEqualizer C (@PullbackProduct C HT HPb) HPb.

(** These Type-valued implications convert chosen data. They assert no
    equality of records or of the choices made by a round trip. *)
Theorem finite_limit_bases (C : Cat)
  : (HasTerminal C ∧ HasPullback C)
    ↔ (HasTerminal C ∧ HasProduct C ∧ HasEqualizer C).
Proof.
  split.
  - intros [HT HPb].
    exact (HT, (@PullbackProduct C HT HPb, @PullbackEqualizer C HT HPb)).
  - intros [HT [HP HE]]. exact (HT, @ProductEqualizerPullback C HP HE).
Defined.
