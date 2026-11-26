From Cats.Set.Relation Require Import StrongNormalization.

(** * Strong-Normalization Interface Checks

    These checks separate carrier, edge and tree universes, then compute
    with transparent countdown trees and a noninjective simulation. They
    concern the reusable relation interface, not a particular calculus. *)

Local Open Scope relation_scope.

(** ** Small Edges over a Larger Carrier

    Fix [r < a < s]. The SN tree must contain the carrier and edge data,
    without forcing their two input universes to coincide. *)

Section SmallEdges.
Universes r a s.
Constraint r < a, a < s.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** Taking a step retains the separated tree universe. *)

Definition small_edge_sn_step {x y : A}
    (p : SN@{a r s} R x) (h : R x y)
  : SN@{a r s} R y
  := sn_step p h.

End SmallEdges.

(** ** Large Edges over a Smaller Carrier

    Fix the reverse order [a < r < s] and check finite-path inheritance. *)

Section LargeEdges.
Universes a r s.
Constraint a < r, r < s.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** Paths preserve SN without identifying carrier and edge bounds. *)

Definition large_edge_sn_path {x y : A}
    (h : (R^*) x y) (p : SN@{a r s} R x)
  : SN@{a r s} R y
  := sn_rtc h p.

End LargeEdges.

(** ** Pullback to Smaller Trees

    Fix a target carrier, edges and tree strictly larger than the source
    tree. A simulation constructs source trees from target trees; it does
    not resize a target tree or impose a bound from target to source. *)

Section SmallerPullback.
Universes a r s b q t.
Constraint a < r, r < s, s < b, b < q, q < t.
Context (A : Type@{a}) (B : Type@{b}).
Context (R : A → A → Type@{r}) (S : B → B → Type@{q}).
Context (f : A → B) (h : ∀ x y, R x y → S (f x) (f y)).

(** The inferred simulation interface keeps the two tree bounds separate. *)

Definition simulation_smaller_tree (x : A) (p : SN@{b q t} S (f x))
  : SN@{a r s} R x
  := sn_simulation f h x p.

End SmallerPullback.

(** ** Independent Components with Different Witness Sizes

    Fix [a < r < b < q < s < t]. The component trees live at [t], while
    the combined tree can live at [s]. Induction can also return small
    computational data despite the size of the input trees. *)

Section IndependentSizes.
Universes a r b q s t.
Constraint a < r, r < b, b < q, q < s, s < t.
Context (A : Type@{a}) (B : Type@{b}).
Context (R : A → A → Type@{r}) (S : B → B → Type@{q}).

(** The product tree stores product steps, with no dependence on the size
    of the input trees used to construct it. *)

Definition independent_product_sn {x : A} (p : SN@{a r t} R x)
    {y : B} (q : SN@{b q t} S y)
  : SN@{b q s} (ProductStep R S) (x, y)
  := sn_product p q.

(** Nested induction can return a small value without resizing its inputs. *)

Definition independent_small_result {x : A} (p : SN@{a r t} R x)
    {y : B} (q : SN@{b q t} S y)
  : nat
  := sn_pair_induction (λ _ _, nat) (λ _ _ _ _, 0) p q.

End IndependentSizes.

(** ** Transparent Computations

    Countdown steps carry arbitrary natural-number tags. A simulated
    carrier adds a Boolean label that may change on every step; projecting
    the counter preserves steps without being injective. *)

Section Computations.

(** Step evidence retains its tag as ordinary Type-valued data. *)

Definition Countdown (n m : nat)
  : Type
  := (n = S m) ∧ nat.

(** Structural induction gives a transparent tree for every counter. *)

Definition countdown_sn (n : nat)
  : SN Countdown n.
Proof.
  induction n as [| n ih]; apply sn_intro; intros m [e tag].
  - discriminate e.
  - injection e as e. subst m. exact ih.
Defined.

(** Selecting a branch computes to the predecessor's existing tree. *)

Example countdown_step_computes
  : sn_step (countdown_sn 2) (eq_refl, 37) = countdown_sn 1.
Proof. reflexivity. Qed.

(** Simulation allows arbitrary changes to the unused Boolean label. *)

Definition tagged_countdown_sn (p : nat * bool)
  : SN (λ x y, Countdown (fst x) (fst y)) p
  := sn_simulation fst (λ _ _ h, h) p (countdown_sn (fst p)).

(** Pullback and step selection remain computational even across labels. *)

Example simulation_step_computes
  : sn_step (tagged_countdown_sn (2, true))
      (y := (1, false)) (eq_refl, 11) =
      tagged_countdown_sn (1, false).
Proof. reflexivity. Qed.

(** Independent components can interleave left and right steps. *)

Definition countdown_product_sn
  : SN (ProductStep Countdown Countdown) (2, 3)
  := sn_product (countdown_sn 2) (countdown_sn 3).

(** Projecting after a left step produces a tree for the new left counter. *)

Definition countdown_product_reduct_sn
  : SN Countdown 1
  := sn_product_left
      (sn_step countdown_product_sn (y := (1, 3))
        (inl ((eq_refl, 19), eq_refl))).

End Computations.
