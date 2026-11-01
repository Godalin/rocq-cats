From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Pullback
  Cat.Fibration Cat.Comprehension.
From Cats Require Import Instance.Set.Core Instance.Set.Fam.Core Instance.Set.Fam.Cat
  Instance.Set.Fam.Reindex Instance.Set.Fam.Fibration Instance.Set.Fam.Section.

(** * Comprehension of Coherent Families

    Every cartesian family morphism gives a pullback of total spaces. It
    factors through the canonical reindexing by an isomorphism over the identity. *)

Definition fam_comprehension_universal : is_comprehension FamProjectionN.
Proof.
  intros U V φ Hφ.
  pose (f := famF_base φ).
  assert (H : fmap FamBaseF (fam_reindex V f) ∘ id ≈ fmap FamBaseF φ).
  { intros x. reflexivity. }
  pose (k := cartesian_factor (fam_reindex_cartesian V f) φ id H).
  assert (Hk_iso : @is_iso FamCat _ _ k).
  { apply (cartesian_factor_is_iso Hφ (fam_reindex_cartesian V f) id).
    exists id. split; apply comp_id_l. }
  assert (Hk_base : fmap FamBaseF k ≈ id).
  { exact (cartesian_factor_base (fam_reindex_cartesian V f) φ id H). }
  assert (Hk_comp : FamFEq (fam_comp (fam_reindex V f) k) φ).
  { exact (cartesian_factor_comp (fam_reindex_cartesian V f) φ id H). }
  eapply (pullback_iso (C := SetCat) (p1 := sig_base_resp V[f]S)
    (p2 := fam_total_resp (fam_reindex V f))
    (fmap FamTotalF k) (functor_is_iso FamTotalF k Hk_iso)).
  - transitivity (fmap FamBaseF k ∘ FamProjectionN U).
    + exact (nt_naturality FamProjectionN k).
    + rewrite Hk_base, comp_id_l. reflexivity.
  - change (fmap FamTotalF (fam_reindex V f) ∘ fmap FamTotalF k ≈ fmap FamTotalF φ).
    rewrite <- functor_comp, Hk_comp. reflexivity.
  - apply fam_reindex_pullback.
Defined.

Definition FamComprehension : Comprehension FamBaseF :=
  {| comprehension_lifts := FamBaseF_HasCartesianLift
   ; ExtF := FamTotalF
   ; projectionN := FamProjectionN
   ; comprehension_universal := fam_comprehension_universal |}.

(** Terms of the family are exactly sections of its display projection,
    with equality comparing the maps rather than their right-inverse proofs. *)
Definition fam_comprehension_section_iso (U : FamC)
  : SectionS U ≅[SetCat] Sec(π[FamComprehension] U) :=
  section_projection_iso U.
