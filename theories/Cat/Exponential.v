From Cats Require Import Cat.Core Cat.Product.

(** * Exponential Objects *)

Definition is_exponential {C : Cat} `{HP : !HasProduct C}
    (X Y E : Ob) (ev : Hom (E × X) Y) :=
  ∀ Z (f : Hom (Z × X) Y),
    ∃ h : Hom Z E, is_unique (λ h, ev ∘ (h × id) ≈ f) h.

Class HasExponential {C : Cat} (HP : HasProduct C) :=
  { exp : Ob → Ob → Ob
  ; eval {X Y} : Hom (exp Y X × X) Y

  ; exponential_universal {X Y} : is_exponential X Y (exp Y X) eval
  }.

Arguments exponential_universal {_ _ _ _ _} _ _.

Definition curry {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}
    {X Y Z} (f : Hom (Z × X) Y) : Hom Z (exp Y X) :=
  (exponential_universal Z f).1.

Theorem exponential_curry_unique {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
    (f : Hom (Z × X) Y)
  : is_unique (λ h, eval ∘ (h × id) ≈ f) (curry f).
Proof. exact (exponential_universal Z f).2. Qed.

Global Instance exponential_curry_proper {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
  : Proper (@HomEq[Z × X, Y] ==> @HomEq[Z, exp Y X]) curry.
Proof.
  intros f g Hfg.
  destruct (exponential_curry_unique f) as [Hf _].
  apply (exponential_curry_unique g). transitivity f; assumption.
Qed.

Notation "X '^' Y" := (exp X Y)
  (at level 30, right associativity): ob_scope.

Notation "'ƛ' f" := (curry f)
  (at level 35) : hom_scope.

Notation "'@eval' X Y" := (@eval _ _ _ _ X Y)
  (at level 35) : hom_scope.
