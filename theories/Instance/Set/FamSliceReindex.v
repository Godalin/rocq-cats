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

(** * Fibers Commute with Substitution

    Over x, an element (a,p : q a ≈ f x) becomes the pullback point
    (x,a,p⁻¹), together with its reflexive membership over x. *)

Program Definition slice_fiber_reindex_resp@{u p +} {X Y : SetC@{u p}}
    (f : X →r Y) (A : SliceOb SetCat Y) (x : X)
  : (FiberFamS (slice_arrow A))[f]S x →r
      FiberS (slice_arrow (SliceReindexOb (C := SetCat) f A)) x :=
  {| func a := ((x; (a.1; symmetry a.2)); reflS (x := x)) |}.
Next Obligation. intros a b H. split; [reflexivity | exact H]. Defined.

Program Definition slice_fiber_reindex@{u p +} {X Y : SetC@{u p}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : (FiberFamS (slice_arrow A))[f]S →Fam
      FiberFamS (slice_arrow (SliceReindexOb (C := SetCat) f A)) :=
  {| fam_map := slice_fiber_reindex_resp f A |}.
Next Obligation. split; [symmetry; exact p | reflexivity]. Defined.

(** A pullback point need only have an equivalent first coordinate.
    Its fiber-membership witness transports that coordinate along f. *)
Program Definition slice_fiber_reindex_inv_resp@{u p +} {X Y : SetC@{u p}}
    (f : X →r Y) (A : SliceOb SetCat Y) (x : X)
  : FiberS (slice_arrow (SliceReindexOb (C := SetCat) f A)) x →r
      (FiberFamS (slice_arrow A))[f]S x :=
  {| func a := (a.1.2.1; _) |}.
Next Obligation.
  transitivity (f a.1.1).
  - symmetry. exact a.1.2.2.
  - apply func_proper. exact a.2.
Defined.
Next Obligation. intros a b H. exact (snd H). Defined.

Program Definition slice_fiber_reindex_inv@{u p +} {X Y : SetC@{u p}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : FiberFamS (slice_arrow (SliceReindexOb (C := SetCat) f A)) →Fam
      (FiberFamS (slice_arrow A))[f]S :=
  {| fam_map := slice_fiber_reindex_inv_resp f A |}.
Next Obligation. reflexivity. Defined.

Definition slice_fiber_reindex_iso@{u p +} {X Y : SetC@{u p}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : @is_iso (FamSCat X) _ _ (slice_fiber_reindex f A).
Proof.
  exists (slice_fiber_reindex_inv f A). split.
  - intros x a. cbn. reflexivity.
  - intros x [[y [a q]] r]. split; [symmetry; exact r | reflexivity].
Defined.

Program Definition SliceFamReindexN@{u p +} {X Y : SetC@{u p}} (f : X →r Y)
  : (FamReindexF f ∘F SliceFamF Y) => (SliceFamF X ∘F SliceReindexF (C := SetCat) f) :=
  {| nt := slice_fiber_reindex f |}.
Next Obligation. intros x a. split; reflexivity. Defined.

Definition slice_fam_reindex_nat_iso@{u p +} {X Y : SetC@{u p}} (f : X →r Y)
  : (FamReindexF f ∘F SliceFamF Y) ≅N (SliceFamF X ∘F SliceReindexF (C := SetCat) f) :=
  (SliceFamReindexN f; slice_fiber_reindex_iso f).

(** ** Compatibility with the Two Round-trip Comparisons

    The sum and fiber base-change comparisons give the same map after
    the slice round trip. The family round trip is likewise preserved,
    using the specified inverse fiber comparison to match its endpoints. *)

Theorem slice_fam_reindex_fiber_total@{u p +} {X Y : SetC@{u p}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : slice_map (slice_comp (C := SetCat)
      (slice_reindex_map (C := SetCat) f (fiber_total_slice A))
      (fam_sum_reindex f (FiberFamS (slice_arrow A)))) ≈f
    slice_map (slice_comp (C := SetCat)
      (fiber_total_slice (SliceReindexOb (C := SetCat) f A))
      (fam_sum_map (slice_fiber_reindex f A))).
Proof. intros [x [a q]]. split; reflexivity. Qed.

Theorem slice_fam_reindex_total_fiber@{u p +} {X Y : SetC@{u p}}
    (f : X →r Y) (A : FamS Y)
  : fam_map_comp (fam_map_reindex f (total_fiber_elim A))
      (fam_map_comp (slice_fiber_reindex_inv f (FamSumOb A))
        (slice_fiber_map (fam_sum_reindex f A))) ≈Fam total_fiber_elim A[f]S.
Proof.
  intros x [[y a] q]. cbn. apply transpS_witness_independent.
Qed.
