From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Product Cat.Exponential.
From Cats Require Import Instance.Set.Core Instance.Set.Adjunction.

(** * Exponential Hom-Setoid Correspondence

    The source category is arbitrary. [SetCat] is used only to express an
    isomorphism of its hom-setoids; no chosen setoid CCC model is enabled.
    Naturality in the context and result object is expressed by
    [exponential_curry_comp_r] and [exponential_curry_comp_l]. *)

Section ExponentialHom.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

Definition exponential_hom_iso {X Y Z : @Ob C}
  : HomSet (Z × X) Y ≅[SetCat] HomSet Z (Y ^ X).
Proof.
  exists exponential_curry_resp, exponential_uncurry_resp. split.
  - intros f. apply exponential_β.
  - intros g. apply exponential_η.
Defined.

Definition exponential_hom_nat_iso@{u p +} (X : @Ob C)
  : @NatIso _ SetCat@{u p _ _ _ _ _}
      (LeftHomF (-× X)) (RightHomF (-^ X)) :=
  adjunction_hom_nat_iso (ProductExponentialAdjunction X).

End ExponentialHom.
