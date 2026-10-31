From Cats Require Import Cat.Core Instance.Set.Core Cat.Pullback.

(** * Pullbacks in the category of setoids

    Equality compares the two coordinates, not the witnesses that their images
    agree. This gives a constructive pullback without proof irrelevance. *)

Definition PbS {X Y Z : SetC} (f : X →r Z) (g : Y →r Z) : SetC.
Proof.
  refine {| carrier := ∃ x : X, ∃ y : Y, f x ≈S g y
          ; carrier_equiv u v := u.1 ≈S v.1 ∧ u.2.1 ≈S v.2.1 |}.
  split.
  - intros u. split; reflexivity.
  - intros u v [H1 H2]. split; symmetry; assumption.
  - intros u v w [H1 H2] [H3 H4]. split; etransitivity; eassumption.
Defined.

Definition pb1_resp {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : PbS f g →r X.
Proof.
  unshelve refine (@Build_FunS_resp (PbS f g) X (λ u, u.1) _).
  intros u v [H1 H2]. exact H1.
Defined.

Definition pb2_resp {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : PbS f g →r Y.
Proof.
  unshelve refine (@Build_FunS_resp (PbS f g) Y (λ u, u.2.1) _).
  intros u v [H1 H2]. exact H2.
Defined.

Definition pb_resp {X Y Z P : SetC} {f : X →r Z} {g : Y →r Z}
    (p1 : P →r X) (p2 : P →r Y) (HP : f ∘ p1 ≈ g ∘ p2)
    : P →r PbS f g.
Proof.
  unshelve refine (@Build_FunS_resp P (PbS f g)
    (λ u, (p1 u; (p2 u; HP u))) _).
  intros u v Huv. split; apply func_proper; exact Huv.
Defined.

Definition SetCat_HasPullback : HasPullback SetCat.
Proof.
  refine {| Pb := λ X Y Z f g, PbS f g
          ; pb1 := λ X Y Z f g, pb1_resp f g
          ; pb2 := λ X Y Z f g, pb2_resp f g |}.
  intros X Y Z f g. split.
  - intros u. exact u.2.2.
  - intros P p1 p2 HP. exists (pb_resp p1 p2 HP). split.
    + split; intros u; reflexivity.
    + intros k [H1 H2] u. split; [exact (H1 u) | exact (H2 u)].
Defined.
