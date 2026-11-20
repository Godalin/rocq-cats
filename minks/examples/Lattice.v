From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

Set Universe Polymorphism.

(** * The lattice hierarchy

    Choose a partial order on a setoid. Add meets and joins independently,
    then extend the lattice by separately choosing a bottom and a top. *)

(** * 格的层级

    在广集上选取偏序，分别加入交与并，再为格独立选取底元和顶元。 *)

(** Choose a relation on the carrier. *)

(** 在载体上选取一个关系。 *)

Class HasOrder@{u o} (A : Type@{u})
  :=
  { leq : A → A → Type@{o}
  }.

Arguments leq {_ _} _ _.

(** Relate the chosen order to the setoid equality. *)

(** 将选取的偏序与广集相等联系起来。 *)

Class IsPoset@{u e o} (A : Type@{u})
    `(E : !HasEquiv@{u e} A) `(O : !HasOrder@{u o} A)
  :=
  { leq_of_equiv : ∀ x y, equiv x y → leq x y
  ; leq_trans : ∀ x y z, leq x y → leq y z → leq x z
  ; leq_antisym : ∀ x y, leq x y → leq y x → equiv x y
  }.

(** Choose greatest lower bounds for the selected order. *)

(** 为选定的序选取最大下界。 *)

Class HasMeet@{u o} (A : Type@{u}) `(O : !HasOrder@{u o} A)
  :=
  { meet : A → A → A
  ; meet_leq_l : ∀ x y, leq (meet x y) x
  ; meet_leq_r : ∀ x y, leq (meet x y) y
  ; leq_meet : ∀ x y z, leq z x → leq z y → leq z (meet x y)
  }.

Arguments meet {_ _ _} _ _.

(** Choose least upper bounds for the same order. *)

(** 为同一选定的序选取最小上界。 *)

Class HasJoin@{u o} (A : Type@{u}) `(O : !HasOrder@{u o} A)
  :=
  { join : A → A → A
  ; leq_join_l : ∀ x y, leq x (join x y)
  ; leq_join_r : ∀ x y, leq y (join x y)
  ; join_leq : ∀ x y z, leq x z → leq y z → leq (join x y) z
  }.

Arguments join {_ _ _} _ _.

(** Choose a bottom for the selected order and witness its lower bound law. *)

(** 在选定的序上选取底元，并提供它小于等于每个元素的见证。 *)

Class HasBottom@{u o} (A : Type@{u}) `(O : !HasOrder@{u o} A)
  :=
  { bottom : A
  ; bottom_leq : ∀ x : A, leq bottom x
  }.

(** Choose a top for the selected order and witness its upper bound law. *)

(** 在选定的序上选取顶元，并提供每个元素小于等于它的见证。 *)

Class HasTop@{u o} (A : Type@{u}) `(O : !HasOrder@{u o} A)
  :=
  { top : A
  ; leq_top : ∀ x : A, leq x top
  }.

(** Both bounds extend the lattice on its already selected order. *)

(** 两个界都在格已选定的序上扩展。 *)

Minks.Struct Poset extends SetC
  with  hasOrder : HasOrder [carrier],
        isPoset : IsPoset [carrier, hasEquiv, hasOrder].

Minks.Struct MeetSemilattice extends Poset
  with  hasMeet : HasMeet [carrier, hasOrder].
Minks.Struct JoinSemilattice extends Poset
  with  hasJoin : HasJoin [carrier, hasOrder].
Minks.Struct Lattice extends MeetSemilattice, JoinSemilattice.

Minks.Struct LatticeWithBottom extends Lattice
  with  hasBottom : HasBottom [carrier, hasOrder].
Minks.Struct LatticeWithTop extends Lattice
  with  hasTop : HasTop [carrier, hasOrder].
Minks.Struct BoundedLattice extends LatticeWithBottom, LatticeWithTop.

Minks.Inspect BoundedLattice.

(** The two inheritance paths reconstruct the same lattice. *)

(** 两条继承路径重建同一个格。 *)

Definition bounded_lattice_coherence (L : BoundedLattice)
  : LatticeWithBottomToLattice (BoundedLatticeToLatticeWithBottom L) =
      LatticeWithTopToLattice (BoundedLatticeToLatticeWithTop L)
  := eq_refl.

(** The order and meet methods use the unique instances directly. *)

(** 序和交的字段可以直接使用唯一的实例。 *)

Definition meet_below_join (L : BoundedLattice) (x y : L)
  : leq (meet x y) (join x y)
  := leq_trans _ _ _ (meet_leq_l x y) (leq_join_l x y).

(** The expected carrier selects each bound and its law. *)

(** 从预期的载体推断对应的界和定律。 *)

Definition selected_bottom_law (L : BoundedLattice) (x : L)
  : leq bottom x
  := bottom_leq x.

Definition selected_top_law (L : BoundedLattice) (x : L)
  : leq x top
  := leq_top x.

(** Inference uses exactly the choices stored in the record. *)

(** 推断使用记录中保存的两份选定值。 *)

Definition bound_laws_use_fields (L : BoundedLattice) (x : L)
  : selected_bottom_law L x =
      @bottom_leq L (BoundedLattice_hasOrder L) (BoundedLattice_hasBottom L) x
    ∧ selected_top_law L x =
      @leq_top L (BoundedLattice_hasOrder L) (BoundedLattice_hasTop L) x
  := conj eq_refl eq_refl.
