From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Bicategory Cat.ThinBicat.
From Cats Require Import Cat.Pullback Instance.Set.Core Instance.Set.Pullback.
From Cats Require Import Instance.Set.FamSliceReindex.

(** Guard against identifying morphism and equivalence-witness universes
    when a construction instantiates a bare [Cat]. Test both orderings. *)
Section CategoryLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p <= l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).

Definition high_eq_id := @IdF C.
Definition low_eq_id := @IdF D.
Definition high_eq_product := C ×C C.
Definition low_eq_product := D ×C D.
Definition high_eq_functors := Fct C C.
Definition low_eq_functors := Fct D D.
Definition high_eq_thin : Bicat@{o h p Set _ _ _} := ThinBicat C.
Definition low_eq_thin := ThinBicat D.
End CategoryLevels.

(** The same hom-category must retain distinct 1-cell, 2-cell and
    2-cell-equivalence levels through the bicategory projections. *)
Section BicategoryLevels.
Universe o h t p a b l.
Constraint o < h.
Constraint h < t.
Constraint t < p.
Constraint p < a.
Constraint a <= b.
Constraint p <= l.
Context (K : Bicat@{o h t p a b l}).

Definition independent_hom (X Y : ObB K) : Cat@{h t p l l} := HomCat X Y.
Definition independent_cells (X Y : ObB K) : Type@{h} := Cell1 X Y.
End BicategoryLevels.

(** The chosen pullback instance formerly collapsed these two levels. *)
Section SetoidPullbackLevels.
Universe u p.
Constraint p < u.
Context (X Y : SetC@{u p}) (f : X →r Y).
Definition distinct_setoid_pullbacks : HasPullback (SetCat@{_ _ _ _ _ u p})
  := SetCat_HasPullback.
Definition distinct_sum_reindex := fam_sum_reindex_nat_iso f.
End SetoidPullbackLevels.
