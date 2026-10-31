From Cats Require Import Cat.Core Instance.Set.Core Cat.Pullback.

(** * Pullbacks in the category of setoids

    Equality compares the two coordinates, not the witnesses that their images
    agree. This gives a constructive pullback without proof irrelevance. *)

Program Definition PbS {X Y Z : SetC} (f : X →r Z) (g : Y →r Z) : SetC :=
  {| carrier := ∃ x : X, ∃ y : Y, f x ≈S g y
   ; carrier_equiv u v := u.1 ≈S v.1 ∧ u.2.1 ≈S v.2.1 |}.
Next Obligation.
  split.
  - intros u. split; reflexivity.
  - intros u v [H1 H2]. split; symmetry; assumption.
  - intros u v w [H1 H2] [H3 H4]. split; etransitivity; eassumption.
Defined.

Program Definition pb1_resp {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : PbS f g →r X := {| func u := u.1 |}.
Next Obligation.
  intros u v [H1 H2]. exact H1.
Defined.

Program Definition pb2_resp {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : PbS f g →r Y := {| func u := u.2.1 |}.
Next Obligation.
  intros u v [H1 H2]. exact H2.
Defined.

Program Definition pb_resp {X Y Z P : SetC} {f : X →r Z} {g : Y →r Z}
    (p1 : P →r X) (p2 : P →r Y) (HP : f ∘ p1 ≈ g ∘ p2)
    : P →r PbS f g := {| func u := (p1 u; (p2 u; HP u)) |}.
Next Obligation.
  intros u v Huv. split; apply func_proper; exact Huv.
Defined.

Program Definition SetCat_HasPullback@{u p +}
  : HasPullback (SetCat@{_ _ _ _ _ u p}) :=
  {| Pb X Y Z f g := PbS f g
   ; pb1 X Y Z f g := pb1_resp f g
   ; pb2 X Y Z f g := pb2_resp f g |}.
Next Obligation.
  split.
  - intros u. exact u.2.2.
  - intros P p1 p2 HP. exists (pb_resp p1 p2 HP). split.
    + split; intros u; reflexivity.
    + intros k [H1 H2] u. split; [exact (H1 u) | exact (H2 u)].
Defined.
