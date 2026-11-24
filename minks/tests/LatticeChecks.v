From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import
  Algebra
  Lattice.

Set Universe Polymorphism.

(** ** Checking the selected components

    The two inheritance paths reconstruct the same lattice. *)

Definition bounded_lattice_coherence (L : BoundedLattice)
  : LatticeWithBottomToLattice (BoundedLatticeToLatticeWithBottom L) =
      LatticeWithTopToLattice (BoundedLatticeToLatticeWithTop L)
  := eq_refl.

(** Inference uses exactly the choices stored in the record. *)

Definition bound_laws_use_fields (L : BoundedLattice) (x : L)
  : selected_bottom_law L x =
      @bottom_leq L (BoundedLattice_hasOrder L) (BoundedLattice_hasBottom L) x
    ∧ selected_top_law L x =
      @leq_top L (BoundedLattice_hasOrder L) (BoundedLattice_hasTop L) x
  := conj eq_refl eq_refl.

(** Both complete branches read the same chosen order. *)

Example complete_lattice_order_coherence (L : CompleteLattice)
  : CompleteJoinSemilattice_hasOrder (CompleteLatticeToCompleteJoinSemilattice L)
    = CompleteMeetSemilattice_hasOrder (CompleteLatticeToCompleteMeetSemilattice L)
  := eq_refl.

(** The binary operations of the finite view compute by the chosen family
    operations. *)

Example complete_lattice_meet_computes (L : CompleteLattice) (x y : L)
  : @meet L (CompleteLattice_hasOrder L)
      (Lattice_hasMeet (CompleteLatticeToLattice L)) x y
    = ameet (fun b : bool => if b then x else y)
  := eq_refl.

Example complete_lattice_join_computes (L : CompleteLattice) (x y : L)
  : @join L (CompleteLattice_hasOrder L)
      (Lattice_hasJoin (CompleteLatticeToLattice L)) x y
    = ajoin (fun b : bool => if b then x else y)
  := eq_refl.
