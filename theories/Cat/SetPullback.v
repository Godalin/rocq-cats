From Cats Require Import Cat.Core Cat.Set Cat.Pullback.

(** * Pullbacks in the category of setoids

    Equality compares the two coordinates, not the witnesses that their images
    agree. This gives a constructive pullback without proof irrelevance. *)

Definition pullback_setoid {X Y Z : SetC} (f : X →r Z) (g : Y →r Z) : SetC.
Proof.
  refine {| carrier := ∃ x : X, ∃ y : Y, f x ≈S g y
          ; carrier_equiv u v := u.1 ≈S v.1 ∧ u.2.1 ≈S v.2.1 |}.
  split.
  - intros u. split; reflexivity.
  - intros u v [H1 H2]. split; symmetry; assumption.
  - intros u v w [H1 H2] [H3 H4]. split; etransitivity; eassumption.
Defined.

Definition set_pb1 {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : pullback_setoid f g →r X.
Proof.
  unshelve refine (@Build_FunS_resp (pullback_setoid f g) X (λ u, u.1) _).
  intros u v [H1 H2]. exact H1.
Defined.

Definition set_pb2 {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : pullback_setoid f g →r Y.
Proof.
  unshelve refine (@Build_FunS_resp (pullback_setoid f g) Y (λ u, u.2.1) _).
  intros u v [H1 H2]. exact H2.
Defined.

Definition set_pb {X Y Z P : SetC} {f : X →r Z} {g : Y →r Z}
    (p1 : P →r X) (p2 : P →r Y) (HP : f ∘ p1 ≈ g ∘ p2)
    : P →r pullback_setoid f g.
Proof.
  unshelve refine (@Build_FunS_resp P (pullback_setoid f g)
    (λ u, (p1 u; (p2 u; HP u))) _).
  intros u v Huv. split; apply func_proper; exact Huv.
Defined.

Definition set_pullbacks : HasPullback SetCat.
Proof.
  refine {| Pb := λ X Y Z f g, pullback_setoid f g
          ; pb1 := λ X Y Z f g, set_pb1 f g
          ; pb2 := λ X Y Z f g, set_pb2 f g
          ; pb := λ X Y Z f g P p1 p2 HP, set_pb p1 p2 HP |}.
  - intros X Y Z f g u. exact u.2.2.
  - intros X Y Z f g P p1 p2 HP. split.
    + split; intros u; reflexivity.
    + intros k [H1 H2] u. split; [exact (H1 u) | exact (H2 u)].
Defined.
