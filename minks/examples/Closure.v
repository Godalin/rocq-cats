From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import
  Algebra
  Lattice.

Set Universe Polymorphism.

(** * Closure operators and their closed points

    Append an endomap to a fixed order, then append an element to the
    resulting closure operator. A closure sends each element to its least
    closed upper bound. *)

(** Specify monotonicity of a supplied endomap. *)

Minks.Mixin IsMonotone (A : Type) (f : A → A)
  extends HasOrder A
  :=
  { monotone_leq : ∀ x y, leq x y → leq (f x) (f y) }.

Print IsMonotone.

(** A closure uses a monotone map and a poset on the same order. The map
    also satisfies extensivity and idempotence. *)

Minks.Mixin IsClosureOp (A : Type) (f : A → A)
  extends IsPoset A, IsMonotone A f
  :=
  { closure_extensive : ∀ x, leq x (f x)
  ; closure_idem : ∀ x, f (f x) ≈ f x
  }.

(** Extend the inherited map and laws by a supplied fixed point. *)

Minks.Mixin IsClosedPoint (A : Type) (f : A → A) (x : A)
  extends IsClosureOp A f
  :=
  { closed_point : f x ≈ x }.

(** ** Least closed upper bounds

    Fix a closure operator on a poset. Its image is closed, and
    monotonicity bounds that image by every closed upper bound. *)

Section ClosureLaws.
Context (A : Type) (f : A → A)
  `{O : !HasOrder A}
  `{E : !HasEquiv A} `{P : !@IsPoset A E O}
  `{M : !@IsMonotone A f O} `{C : !@IsClosureOp A f O E P M}.

(** The image of each element is a closed point. *)

Definition closure_closed (x : A)
  : @IsClosedPoint A f (f x) O E P M C
  :=
  {| closed_point := closure_idem x
  |}.

(** Every closed upper bound of an element also bounds its closure. *)

Definition closure_least (x y : A)
    `{Y : !@IsClosedPoint A f y O E P M C} (xy : leq x y)
  : leq (f x) y
  := leq_trans (f x) (f y) y (monotone_leq x y xy)
       (leq_of_equiv (f y) y closed_point).

End ClosureLaws.

Print closure_closed.

(** ** Closing by joining with a fixed element

    In any lattice, joining with a fixed element gives a closure operator.
    Use the selected join and the same order for all its laws. *)

Section JoinClosure.
Context (L : Lattice).

(** Joining with a fixed element is monotone. *)

Definition join_monotone (a : L)
  : IsMonotone L (fun x => join x a).
Proof.
  constructor. intros x y xy. apply join_leq.
  - exact (leq_trans x y (join y a) xy (leq_join_l y a)).
  - apply leq_join_r.
Defined.

(** Joining with the same element is extensive and idempotent. *)

Definition join_closure (a : L)
  : IsClosureOp L (fun x => join x a) (isMonotone := join_monotone a).
Proof.
  constructor.
  - intro x. apply leq_join_l.
  - intro x. apply leq_antisym.
    + apply join_leq.
      * apply leq_of_equiv, equiv_refl.
      * apply leq_join_r.
    + apply leq_join_l.
Defined.

End JoinClosure.
