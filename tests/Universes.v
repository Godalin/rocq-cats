From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Bicategory Cat.ThinBicat.
From Cats Require Import Cat.CCC.
From Cats Require Import DTT.CwF.
From Cats Require Import Cat.Pullback Instance.Set.Core Instance.Set.Pullback.
From Cats Require Import Instance.Set.FamSlice Instance.Set.FamSliceReindex.
From Cats Require Import Instance.Set.Fam Instance.Set.CwF.

(** Basic sets and their category accept both carrier/equality orderings. *)
Section SetLevels.
Universe u p.
Constraint Set < u.
Constraint u < p.
Context (X : SetC@{u p}) (Y : SetC@{p u}).

Definition high_eq_set_id : X →r X := id_resp.
Definition low_eq_set_id : Y →r Y := id_resp.
Definition high_eq_sets := SetCat@{u p _ _ _ _ _}.
Definition low_eq_sets := SetCat@{p u _ _ _ _ _}.
End SetLevels.

(** Guard against identifying morphism and equivalence-witness universes
    when a construction instantiates a bare [Cat]. Test both orderings. *)
Section CategoryLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p <= l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).

Definition high_eq_hom (X Y : @Ob C) : SetC@{h p} := HomSet X Y.
Definition low_eq_hom (X Y : @Ob D) : SetC@{p h} := HomSet X Y.
Definition high_eq_id := @IdF C.
Definition low_eq_id := @IdF D.
Definition high_eq_product := C ×C C.
Definition low_eq_product := D ×C D.
Definition high_eq_functors := Fct C C.
Definition low_eq_functors := Fct D D.
Definition high_eq_ccc := CCC C.
Definition low_eq_ccc := CCC D.
Definition high_eq_cwf := CwF C.
Definition low_eq_cwf := CwF D.
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
Context (K : Bicat@{o h t p a b l}) (L : Bicat@{o h p t a b l}).

Definition independent_hom (X Y : ObB K) : Cat@{h t p l l} := HomCat X Y.
Definition independent_hom_reverse (X Y : ObB L) : Cat@{h p t l l} := HomCat X Y.
Definition independent_cells (X Y : ObB K) : Type@{h} := Cell1 X Y.
End BicategoryLevels.

(** The chosen pullback instance formerly collapsed these two levels. *)
Section SetoidPullbackLevels.
Universe u p.
Constraint p < u.
Context (X Y : SetC@{u p}) (f : X →r Y).
Definition distinct_setoid_pullbacks : HasPullback (SetCat@{u p _ _ _ _ _})
  := SetCat_HasPullback.
Definition distinct_sum_reindex := fam_sum_reindex_nat_iso f.
Definition distinct_fam_slice_equivalence := fam_slice_equiv X.
End SetoidPullbackLevels.

(** Codes can be larger than contexts. Decoded fibers determine the two
    context levels, which remain independent in either ordering. *)
Section CodeModelLevels.
Universe u p c q l.
Constraint Set < u.
Constraint u < p.
Constraint p < c.
Constraint c < q.
Constraint q < l.
Context (Code : SetC@{c q}) (Code' : SetC@{q c}).
Context (El : FamS@{c q l u p} Code) (El' : FamS@{c q l p u} Code).
Context (El'' : FamS@{q c l u p} Code').

Definition high_eq_code_model : CwF (SetCat@{u p _ _ _ _ _}) := SetCwF El.
Definition low_eq_code_model : CwF (SetCat@{p u _ _ _ _ _}) := SetCwF El'.
Definition reverse_code_model : CwF (SetCat@{u p _ _ _ _ _}) := SetCwF El''.
End CodeModelLevels.
