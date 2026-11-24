From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

Set Universe Polymorphism.

(** * The lattice hierarchy

    Choose a partial order on a setoid. Add meets and joins independently,
    then choose bounds and the joins and meets of arbitrary families. *)

(** Choose a relation on the carrier. *)

Minks.Mixin HasOrder (A : Type)
  :=
  { leq : A → A → Type
  }.
Arguments leq {_ _} _ _.

(** Relate the chosen order to the setoid equality. *)

Minks.Mixin IsPoset (A : Type)
  extends HasEquiv A, HasOrder A
  :=
  { leq_of_equiv : ∀ x y, x ≈ y → leq x y
  ; leq_trans : ∀ x y z, leq x y → leq y z → leq x z
  ; leq_antisym : ∀ x y, leq x y → leq y x → x ≈ y
  }.

(** Choose greatest lower bounds for the selected order. *)

Minks.Mixin HasMeet (A : Type)
  extends HasOrder A
  :=
  { meet : A → A → A
  ; meet_leq_l : ∀ x y, leq (meet x y) x
  ; meet_leq_r : ∀ x y, leq (meet x y) y
  ; leq_meet : ∀ x y z, leq z x → leq z y → leq z (meet x y)
  }.
Arguments meet {_ _ _} _ _.

(** Choose least upper bounds for the same order. *)

Minks.Mixin HasJoin (A : Type)
  extends HasOrder A
  :=
  { join : A → A → A
  ; leq_join_l
    : ∀ x y, leq x (join x y)
  ; leq_join_r
    : ∀ x y, leq y (join x y)
  ; join_leq
    : ∀ x y z, leq x z → leq y z → leq (join x y) z
  }.
Arguments join {_ _ _} _ _.

(** Choose least upper bounds at an index universe that contains the carrier. *)

Minks.Mixin HasAJoin@{u o i | u <= i} (A : Type@{u})
  extends HasOrder@{u o} A
  :=
  { ajoin {I : Type@{i}} (f : I → A) : A
  ; leq_ajoin {I : Type@{i}} (f : I → A) (k : I)
    : leq (f k) (ajoin f)
  ; ajoin_leq {I : Type@{i}} (f : I → A) (b : A)
    : (∀ k, leq (f k) b) → leq (ajoin f) b
  }.

(** Choose greatest lower bounds at an index universe that contains the carrier. *)

Minks.Mixin HasAMeet@{u o i | u <= i} (A : Type@{u})
  extends HasOrder@{u o} A
  :=
  { ameet {I : Type@{i}} (f : I → A) : A
  ; ameet_leq {I : Type@{i}} (f : I → A) (k : I)
    : leq (ameet f) (f k)
  ; leq_ameet {I : Type@{i}} (f : I → A) (b : A)
    : (∀ k, leq b (f k)) → leq b (ameet f)
  }.

(** Restrict the family join to two elements on the same order. *)

Instance HasJoinOfHasAJoin (A : Type) `{O : HasOrder A}
    `{J : !@HasAJoin A O}
  : @HasJoin A O.
Proof.
  refine {| join := fun x y => ajoin (fun b : bool => if b then x else y) |}.
  - intros x y. exact (leq_ajoin _ true).
  - intros x y. exact (leq_ajoin _ false).
  - intros x y z Hx Hy. apply ajoin_leq. intros []; assumption.
Defined.

(** Restrict the family meet to two elements on the same order. *)

Instance HasMeetOfHasAMeet (A : Type) `{O : HasOrder A}
    `{M : !@HasAMeet A O}
  : @HasMeet A O.
Proof.
  refine {| meet := fun x y => ameet (fun b : bool => if b then x else y) |}.
  - intros x y. exact (ameet_leq _ true).
  - intros x y. exact (ameet_leq _ false).
  - intros x y z Hx Hy. apply leq_ameet. intros []; assumption.
Defined.

(** Choose a bottom for the selected order and witness its lower bound law. *)

Minks.Mixin HasBottom (A : Type)
  extends HasOrder A
  :=
  { bottom : A
  ; bottom_leq : ∀ x : A, leq bottom x
  }.

(** Choose a top for the selected order and witness its upper bound law. *)

Minks.Mixin HasTop@{u o} (A : Type@{u})
  extends HasOrder@{u o} A
  :=
  { top : A
  ; leq_top : ∀ x : A, leq x top
  }.

(** ** Finite and complete lattices

    Both bounds extend the lattice on its already selected order. *)

Minks.Struct Poset
  extends SetC
  with  hasOrder : HasOrder,
        isPoset : IsPoset.

Minks.Struct MeetSemilattice
  extends Poset
  with  hasMeet : HasMeet.

Minks.Struct JoinSemilattice
  extends Poset
  with  hasJoin : HasJoin.

Minks.Struct Lattice
  extends MeetSemilattice, JoinSemilattice
  exports HasLattice [carrier],
          IsLattice [isPoset].

Print HasLattice.
Print IsLattice.

Minks.Struct LatticeWithBottom
  extends Lattice
  with  hasBottom : HasBottom.

Minks.Struct LatticeWithTop
  extends Lattice
  with  hasTop : HasTop.

Minks.Struct BoundedLattice
  extends LatticeWithBottom, LatticeWithTop.

(** The complete branches add family bounds to the same chosen poset. *)

Minks.Struct CompleteJoinSemilattice
  extends Poset
  with  hasAJoin : HasAJoin.

Minks.Struct CompleteMeetSemilattice
  extends Poset
  with  hasAMeet : HasAMeet.

Minks.Struct CompleteLattice
  extends CompleteJoinSemilattice,
          CompleteMeetSemilattice
  with    hasBottom : HasBottom,
          hasTop : HasTop
  exports HasCompleteLattice [carrier],
          IsCompleteLattice [isPoset].

(** ** Deriving binary operations

    Read the binary join from the chosen family join. *)

Definition CompleteJoinSemilatticeToJoinSemilattice
    (L : CompleteJoinSemilattice)
  : JoinSemilattice
  := JoinSemilatticeOfPoset L (HasJoinOfHasAJoin L).

(** Read the binary meet from the chosen family meet. *)

Definition CompleteMeetSemilatticeToMeetSemilattice
    (L : CompleteMeetSemilattice)
  : MeetSemilattice
  := MeetSemilatticeOfPoset L (HasMeetOfHasAMeet L).

(** Combine the two derived binary operations on the shared poset. *)

Definition CompleteLatticeToLattice (L : CompleteLattice)
  : Lattice
  := LatticeOfMeetSemilattice (CompleteMeetSemilatticeToMeetSemilattice L)
       (HasJoinOfHasAJoin L).

(** Use the derived operations and the same selected bottom and top. *)

Definition CompleteLatticeToBoundedLattice (L : CompleteLattice)
  : BoundedLattice
  := let F := CompleteLatticeToLattice L in
     BoundedLatticeOfLatticeWithBottom
       (LatticeWithBottomOfLattice F (CompleteLattice_hasBottom L))
       (CompleteLattice_hasTop L).

(** The order and meet methods use the unique instances directly. *)

Definition meet_below_join (L : BoundedLattice) (x y : L)
  : leq (meet x y) (join x y)
  := leq_trans _ _ _ (meet_leq_l x y) (leq_join_l x y).

(** The expected carrier selects each bound and its law. *)

Definition selected_bottom_law (L : BoundedLattice) (x : L)
  : leq bottom x
  := bottom_leq x.

Definition selected_top_law (L : BoundedLattice) (x : L)
  : leq x top
  := leq_top x.

(** ** Subsets of a complete lattice

    Index a subset by the dependent pair of an element and its membership
    witness. The family bounds give the subset bounds directly. *)

Section CompleteLatticeSubsets.
Context (L : CompleteLattice).

(** Select the least upper bound of a Type-valued subset. *)

Definition subset_ajoin (P : L → Type)
  : L
  := ajoin (@projT1 _ P).

(** Every member lies below the selected join. *)

Definition leq_subset_ajoin (P : L → Type) (x : L) (p : P x)
  : leq x (subset_ajoin P)
  := leq_ajoin (@projT1 _ P) (existT P x p).

(** Every upper bound lies above the selected join. *)

Definition subset_ajoin_leq (P : L → Type) (b : L)
    (upper : ∀ x, P x → leq x b)
  : leq (subset_ajoin P) b
  := ajoin_leq (@projT1 _ P) b
       (fun t : sigT P => upper (projT1 t) (projT2 t)).

(** Select the greatest lower bound of the same kind of subset. *)

Definition subset_ameet (P : L → Type)
  : L
  := ameet (@projT1 _ P).

(** The selected meet lies below every member. *)

Definition subset_ameet_leq (P : L → Type) (x : L) (p : P x)
  : leq (subset_ameet P) x
  := ameet_leq (@projT1 _ P) (existT P x p).

(** Every lower bound lies below the selected meet. *)

Definition leq_subset_ameet (P : L → Type) (b : L)
    (lower : ∀ x, P x → leq b x)
  : leq b (subset_ameet P)
  := leq_ameet (@projT1 _ P) b
       (fun t : sigT P => lower (projT1 t) (projT2 t)).

End CompleteLatticeSubsets.

(** Empty families recover the selected bounds in the setoid equality. *)

Definition ajoin_empty (L : CompleteLattice)
  : ajoin (fun t : Empty_set => match t return L with end) ≈ bottom.
Proof.
  apply leq_antisym.
  - apply ajoin_leq. intros k. destruct k.
  - apply bottom_leq.
Defined.

Definition ameet_empty (L : CompleteLattice)
  : ameet (fun t : Empty_set => match t return L with end) ≈ top.
Proof.
  apply leq_antisym.
  - apply leq_top.
  - apply leq_ameet. intros k. destruct k.
Defined.
