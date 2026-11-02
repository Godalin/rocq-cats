From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Adjunction.
From Cats Require Import Instance.Set.Core Instance.Set.Lift.
From Cats Require Export Instance.Set.Hom.

(** * Re-embedding a Hom Isomorphism in an Ambient Set Category

    The chosen adjunction is fixed before the target levels are introduced.
    Native transposes let the resulting isomorphism use either ordering of
    the ambient carrier and equality-witness levels. *)
Section AdjunctionSets.
Context {C D : Cat} {F : Functor C D} {G : Functor D C} (A : F ⊣ G).

Program Definition AdjunctN@{u p +}
  : @Nat _ SetCat@{u p _ _ _ _ _} (LeftHomF F) (RightHomF G) :=
  {| nt X := (adjunct_resp A)^↑S |}.
Next Obligation.
  intros [h]. constructor.
  change ((snd f ∘ h ∘ fmap F (fst f))^♯[A] ≈
    fmap G (snd f) ∘ h^♯[A] ∘ fst f).
  rewrite adjunct_comp_r, adjunct_comp_l. reflexivity.
Defined.

Definition adjunction_hom_nat_iso@{u p +}
  : @NatIso _ SetCat@{u p _ _ _ _ _} (LeftHomF F) (RightHomF G).
Proof.
  exists AdjunctN. intros [X Y].
  exists ((unadjunct_resp A)^↑S). split; intros [f];
    constructor; [exact (adjunction_β A f) | exact (adjunction_η A f)].
Defined.

Definition adjunction_hom_iso@{u p +} (X : @Ob C) (Y : @Ob D)
  : LiftS@{_ _ u p} (HomSet (F X) Y) ≅[SetCat]
      LiftS@{_ _ u p} (HomSet X (G Y)) :=
  (AdjunctN (X, Y); adjunction_hom_nat_iso.2 (X, Y)).

End AdjunctionSets.
