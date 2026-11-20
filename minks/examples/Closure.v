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

(** * 闭包算子与闭点

    在固定序上追加一个自映射，再为得到的闭包算子追加一个元素。
    闭包将每个元素送到它的最小闭上界。 *)

(** Specify monotonicity of a supplied endomap. *)

(** 给定自映射的单调性。 *)

Minks.Mixin IsMonotone (f : A → A)
  extends HasOrder
  :=
  { monotone_leq : ∀ x y, leq x y → leq (f x) (f y) }.

Print IsMonotone.

(** A closure uses a monotone map and a poset on the same order. The map
    also satisfies extensivity and idempotence. *)

(** 闭包的单调映射与偏序共享同一份序，映射另外满足扩张性和幂等性。 *)

Minks.Mixin IsClosureOp
  extends IsPoset, IsMonotone
  :=
  { closure_extensive : ∀ x, leq x (f x)
  ; closure_idem : ∀ x, equiv (f (f x)) (f x)
  }.

(** Extend the inherited map and laws by a supplied fixed point. *)

(** 在继承的映射及定律上追加一个给定的不动点。 *)

Minks.Mixin IsClosedPoint (x : A)
  extends IsClosureOp
  :=
  { closed_point : equiv (f x) x }.

(** ** Least closed upper bounds

    Fix a closure operator on a poset. Its image is closed, and
    monotonicity bounds that image by every closed upper bound. *)

(** ** 最小闭上界

    固定偏序上的闭包算子。闭包的像是闭点，单调性保证它小于等于每个闭上界。 *)

Section ClosureLaws.
Context (A : Type) (f : A → A)
  `{O : !HasOrder A}
  `{E : !HasEquiv A} `{P : !@IsPoset A E O}
  `{M : !@IsMonotone A O f} `{C : !@IsClosureOp A O E P f M}.

(** The image of each element is a closed point. *)

(** 每个元素的闭包都是闭点。 *)

Definition closure_closed (x : A)
  : @IsClosedPoint A O E P f M C (f x)
  :=
  {| closed_point := closure_idem x
  |}.

(** Every closed upper bound of an element also bounds its closure. *)

(** 元素的每个闭上界也是其闭包的上界。 *)

Definition closure_least (x y : A)
    `{Y : !@IsClosedPoint A O E P f M C y} (xy : leq x y)
  : leq (f x) y
  := leq_trans (f x) (f y) y (monotone_leq x y xy)
       (leq_of_equiv (f y) y closed_point).

End ClosureLaws.

Print closure_closed.

(** ** Closing by joining with a fixed element

    In any lattice, joining with a fixed element gives a closure operator.
    Use the selected join and the same order for all its laws. *)

(** ** 与固定元素取并得到闭包

    在任意格上，与固定元素取并给出闭包算子。所有定律使用同一份选定的并和偏序。 *)

Section JoinClosure.
Context (L : Lattice).

(** Joining with a fixed element is monotone. *)

(** 与固定元素取并是单调的。 *)

Definition join_monotone (a : L)
  : IsMonotone L (fun x => join x a).
Proof.
  constructor. intros x y xy. apply join_leq.
  - exact (leq_trans x y (join y a) xy (leq_join_l y a)).
  - apply leq_join_r.
Defined.

(** Joining with the same element is extensive and idempotent. *)

(** 与同一个元素取并满足扩张性和幂等性。 *)

Definition join_closure (a : L)
  : @IsClosureOp L (Lattice_hasOrder L)
      (Lattice_hasEquiv L) (Lattice_isPoset L)
      (fun x => join x a) (join_monotone a).
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
