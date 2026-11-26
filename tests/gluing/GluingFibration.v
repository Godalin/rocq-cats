From Cats Require Import
  Cat.Gluing.Fibration
  Cat.Pullback
  Instance.Set.Core
  Instance.Set.Pullback
  Instance.Bool.Action.
From CatsTests.gluing Require Import
  Gluing.

(** * Gluing Fibration Interfaces and Computation

    Keep independent category sizes, explicit choice and observable
    equality witnesses. A nonidentity boolean action also tests a genuine
    change of base; the gluing functor need not preserve chosen pullbacks. *)

(** ** Independent Source and Target Levels

    Source equality is above its hom carrier, target equality below it.
    Object and auxiliary law levels remain separate across the categories. *)

Section IndependentLevels.
Universes oc hc ec lc od hd ed ld.
Constraint hc < ec, ec < oc, oc < lc.
Constraint ed < hd, hd < od, od < ld.
Constraint lc < od.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F : Fct C D).

(** No chosen structures occur in the candidate equivalence. *)

Definition independent_gluing_cartesian {X Y : Gluing F} (f : Hom X Y)
  : f ⦂ Cart(GluingRightF F) ↔
    is_pullback (fmap F (comma_right f)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left f)
  := gluing_cartesian_iff_pullback F f.

(** Just the required pullback family supplies the chosen lifts. *)

Definition independent_gluing_lifts
    (pullbacks : ∀ (Y : Gluing F) (A : C)
      (σ : Hom A (comma_right_ob Y)),
      ∃ R : D, ∃ r : Hom R (F A), ∃ v : Hom R (comma_left_ob Y),
        is_pullback (fmap F σ) (comma_arrow Y) R r v)
  : HasCartLift (GluingRightF F)
  := GluingRightF_HasCartLift F pullbacks.

End IndependentLevels.

(** ** Reversed Independent Levels

    Reverse both hom/equality orders and the source/target object and law
    orders. The convenience wrapper still preserves the native boundaries. *)

Section ReversedLevels.
Universes oc hc ec lc od hd ed ld.
Constraint ec < hc, hc < oc, oc < lc.
Constraint hd < ed, ed < od, od < ld.
Constraint ld < oc.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F : Fct C D) `{HP : !HasPullback D}.

(** The candidate equivalence also accepts the reversed profile. *)

Definition reversed_gluing_cartesian {X Y : Gluing F} (f : Hom X Y)
  : f ⦂ Cart(GluingRightF F) ↔
    is_pullback (fmap F (comma_right f)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left f)
  := gluing_cartesian_iff_pullback F f.

(** Importing the wrapper must not select lifts automatically. *)

Fail Definition unchosen_gluing_lifts
  : HasCartLift (GluingRightF F)
  := ltac:(typeclasses eauto).

(** Explicit selection reuses all-target pullbacks only when requested. *)

Definition reversed_gluing_lifts
  : HasCartLift (GluingRightF F)
  := GluingRightF_PullbackHasCartLift F.

End ReversedLevels.

(** ** Setoid Factors over an Ignored Tag

    Enable the original setoid pullbacks locally. Equivalent maps can
    change tags and equality witnesses; cartesian factorization compares
    their values rather than their stored proofs. *)

Section SetoidFactors.
Local Instance set_pullbacks
  : HasPullback SetCat
  := SetCat_HasPullback.

(** The lifted object is the original setoid pullback over a tag toggle. *)

Definition TaggedReindexedOb
  : Gluing (@IdF SetCat)
  := GluingPullbackOb IdF (Pb gluing_toggle id) (pb1 _ _).

(** Keep the requested base map exactly, and the second projection on top. *)

Definition tagged_reindex_lift
  : (@Hom (Gluing (@IdF SetCat))) TaggedReindexedOb TaggedGluingObj
  := gluing_pullback_lift IdF TaggedGluingObj gluing_toggle
      (Pb gluing_toggle id) (pb1 _ _) (pb2 _ _) pullback_universal.

(** The candidate cartesian witness needs only this one pullback. *)

Definition tagged_reindex_cartesian
  : tagged_reindex_lift ⦂ Cart(GluingRightF (@IdF SetCat))
  := gluing_pullback_lift_cartesian IdF TaggedGluingObj gluing_toggle
      (Pb gluing_toggle id) (pb1 _ _) (pb2 _ _) pullback_universal.

(** Use the generic cartesian factor; the implementation extracts the
    existing arrow-category mediator. *)

Definition tagged_factor
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedReindexedOb
  := cartesian_factor tagged_reindex_cartesian tagged_gluing_toggle id
      (comp_resp_id_r gluing_toggle).

(** Its top map computes both pullback coordinates. *)

Example tagged_factor_values_compute
  : ((comma_left tagged_factor (3, false)).1,
      (comma_left tagged_factor (3, false)).2.1) =
      ((3, false), (3, true)).
Proof. reflexivity. Defined.

(** The supplied base factor remains the original identity function. *)

Example tagged_factor_base_computes
  : comma_right tagged_factor (3, false) = (3, false).
Proof. reflexivity. Defined.

(** A second factor uses a specified-equal square with different tag data. *)

Definition tagged_identity_factor
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedReindexedOb
  := cartesian_factor tagged_reindex_cartesian id id
      (λ x, (eq_refl, true)).

(** Reuse generic factor respectfulness, including commutativity-witness
    independence; native equality of these square records is unnecessary. *)

Example tagged_factor_respects
  : tagged_factor ≈ tagged_identity_factor.
Proof.
  apply cartesian_factor_proper; [exact tagged_gluing_toggle_equal | reflexivity].
Defined.

(** Recover a target mediator through the reverse candidate theorem.
    Its cone has the identity and the tag toggle as projections. *)

Definition recovered_tagged_mediator
  : TaggedGluingS →r comma_left_ob TaggedReindexedOb
  := (snd (gluing_cartesian_pullback IdF tagged_reindex_lift
      tagged_reindex_cartesian) TaggedGluingS id gluing_toggle
      (λ x, (eq_refl, true))).1.

(** The reverse theorem retains the same transparent coordinate computation. *)

Example recovered_tagged_mediator_computes
  : ((recovered_tagged_mediator (3, false)).1,
      (recovered_tagged_mediator (3, false)).2.1) =
      ((3, false), (3, true)).
Proof. reflexivity. Defined.

(** Membership keeps an observable token. *)

Definition tagged_pullback_token
  : comma_left_ob TaggedReindexedOb
  := ((3, false); ((3, true); (eq_refl, true))).

(** The pullback witness is computational data, not a truncated assertion. *)

Example tagged_pullback_token_computes
  : snd tagged_pullback_token.2.2 = true.
Proof. reflexivity. Defined.

End SetoidFactors.

(** ** A Nonidentity Semantic Action

    The nonidentity loop acts by negation. Its lifted arrow keeps that loop
    as base, and factorization computes a pair with opposite booleans. *)

Section BooleanAction.
Local Instance action_pullbacks
  : HasPullback SetCat
  := SetCat_HasPullback.

(** The semantic object is the identity arrow over the action's object. *)

Program Definition ActionGluingOb
  : Gluing BoolActionF
  :=
  {|comma_left_ob := BoolActionF tt
  ; comma_right_ob := tt
  ; comma_arrow := id
  |}.

(** Its nontrivial square has the semantic action as top side. *)

Program Definition action_square
  : (@Hom (Gluing BoolActionF)) ActionGluingOb ActionGluingOb
  :=
  {|comma_left := fmap BoolActionF bool_loop
  ; comma_right := bool_loop
  |}.
Next Obligation. intros b. reflexivity. Defined.

(** Select the available lift explicitly for this model. *)

Local Instance action_lifts
  : HasCartLift (GluingRightF BoolActionF)
  := GluingRightF_PullbackHasCartLift BoolActionF.

(** The chosen base remains the requested object by native computation. *)

Example action_lift_base_computes
  : cartesian_lift_base (P := GluingRightF BoolActionF)
      (Y := ActionGluingOb) bool_loop = eq_refl.
Proof. reflexivity. Defined.

(** The selected lifting arrow keeps the nonidentity loop. *)

Example action_lift_arrow_computes
  : comma_right (cartesian_lift (P := GluingRightF BoolActionF)
      (Y := ActionGluingOb) bool_loop) = true.
Proof. reflexivity. Defined.

(** Factor the action square over an identity base factor. *)

Definition action_factor
  : (@Hom (Gluing BoolActionF)) ActionGluingOb
      (@CartLift _ _ (GluingRightF BoolActionF) action_lifts
        ActionGluingOb tt bool_loop)
  := cartesian_factor (@cartesian_lift_universal _ _
      (GluingRightF BoolActionF) action_lifts ActionGluingOb tt bool_loop)
      action_square (@Cats.Cat.Core.id BoolGpd tt) (comp_id_r bool_loop).

(** The two pullback coordinates exhibit the nonidentity action. *)

Example action_factor_values_compute
  : ((comma_left action_factor false).1,
      (comma_left action_factor false).2.1) = (false, true).
Proof. reflexivity. Defined.

End BooleanAction.
