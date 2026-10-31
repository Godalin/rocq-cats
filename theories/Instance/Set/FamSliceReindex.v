From Cats Require Import Cat.Core Cat.Slice Cat.SliceReindex Cat.Pullback.
From Cats Require Import Cat.Functor Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Pullback.
From Cats Require Import Instance.Set.Fam Instance.Set.FamCat Instance.Set.FamReindex.
From Cats Require Import Instance.Set.FamFixed Instance.Set.FamSlice.

(** * Total Spaces Commute with Substitution

    Compare the existing family-reindexing pullback with the chosen setoid
    pullback, using the general slice construction. *)

Local Existing Instance SetCat_HasPullback.

Definition fam_sum_reindex@{u p +} {X Y : SetC@{u p}} (f : X →r Y) (A : FamS Y)
  : SliceHom (FamSumOb A[f]S) (FamSumOb A)[f]C :=
  slice_reindex_lift f (FamSumOb A) (B := FamSumOb A[f]S)
    (fam_total_resp (fam_reindex (FixedFamC A) f))
    (fst (fam_reindex_pullback (FixedFamC A) f)).

Definition fam_sum_reindex_iso@{u p +} {X Y : SetC@{u p}} (f : X →r Y) (A : FamS Y)
  : @is_iso (SetCat /C X) _ _ (fam_sum_reindex f A) :=
  slice_reindex_lift_iso f (FamSumOb A) (B := FamSumOb A[f]S)
    (fam_total_resp (fam_reindex (FixedFamC A) f))
    (fst (fam_reindex_pullback (FixedFamC A) f))
    (fam_reindex_pullback (FixedFamC A) f).

Program Definition FamSumReindexN@{u p +} {X Y : SetC@{u p}} (f : X →r Y)
  : (FamSumF X ∘F FamReindexF f) => (SliceReindexF (C := SetCat) f ∘F FamSumF Y) :=
  {| nt := fam_sum_reindex f |}.
Next Obligation. intros [x a]. split; reflexivity. Defined.

Definition fam_sum_reindex_nat_iso@{u p +} {X Y : SetC@{u p}} (f : X →r Y)
  : (FamSumF X ∘F FamReindexF f) ≅N (SliceReindexF (C := SetCat) f ∘F FamSumF Y) :=
  (FamSumReindexN f; fam_sum_reindex_iso f).

(** The natural comparison commutes with the chosen identity and composite
    substitution comparisons. These are equations of maps in the slice. *)
Theorem fam_sum_reindex_id@{u p +} {X : SetC@{u p}} (A : FamS X)
  : slice_map (slice_comp (C := SetCat) (fam_sum_reindex id_resp A)
      (fam_sum_map (fam_map_reindex_id A))) ≈f
      slice_map (slice_reindex_id (C := SetCat) (FamSumOb A)).
Proof. intros [x a]. split; reflexivity. Qed.

Theorem fam_sum_reindex_comp@{u p +} {X Y Z : SetC@{u p}}
    (f : Y →r Z) (g : X →r Y) (A : FamS Z)
  : slice_map (slice_comp (C := SetCat) (fam_sum_reindex (f ∘r g) A)
      (fam_sum_map (fam_map_reindex_comp f g A))) ≈f
    slice_map (slice_comp (C := SetCat)
      (slice_comp (C := SetCat) (slice_reindex_comp (C := SetCat) f g (FamSumOb A))
        (slice_reindex_map (C := SetCat) g (fam_sum_reindex f A)))
      (fam_sum_reindex g A[f]S)).
Proof. intros [x a]. split; reflexivity. Qed.
