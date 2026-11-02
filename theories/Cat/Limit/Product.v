From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Product Cat.Limit.
From Cats Require Import Cat.Adjunction Cat.Limit.Preservation.
From Cats Require Export Cat.Diagram.Shape.

(** * Binary Products as Limits of Discrete Diagrams *)
Section ProductLimits.
Context {C : Cat} {D : Functor PairShape C} {P : @Ob C} (κ : P ⇒Δ D).

Definition product_limit (HP : is_product (D false) (D true) P (κ false) (κ true))
  : is_limit κ.
Proof.
  intros Z μ. destruct (HP Z (μ false) (μ true)) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - intros []; [exact (snd (@this _ _ _ _ _ Hh)) | exact (fst (@this _ _ _ _ _ Hh))].
  - intros g Hg. apply (@that _ _ _ _ _ Hh). split; [exact (Hg false) | exact (Hg true)].
Defined.

Definition limit_product (Hκ : is_limit κ)
  : is_product (D false) (D true) P (κ false) (κ true).
Proof.
  intros Z f g.
  pose (μ := @DiscreteCone C bool D Z
    (λ b, if b as v return Hom Z (D v) then g else f)).
  destruct (Hκ Z μ) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - split; [exact (@this _ _ _ _ _ Hh false) | exact (@this _ _ _ _ _ Hh true)].
  - intros k [Hf Hg]. apply (@that _ _ _ _ _ Hh).
    intros []; [exact Hg | exact Hf].
Defined.

Theorem product_iff_limit
  : is_product (D false) (D true) P (κ false) (κ true) ↔ is_limit κ.
Proof. split; [apply product_limit | apply limit_product]. Defined.

End ProductLimits.

(** Chosen products give all diagrams of this shape a chosen limit.
    These structures must be explicitly enabled. *)
Program Definition ProductDiagramLimit {C : Cat} `{HP : !HasProduct C}
    (D : Functor PairShape C) : HasLimit C D :=
  {| Lim := D false × D true
   ; limit_cone := @DiscreteCone C bool D (D false × D true)
       (λ b, if b as v return Hom (D false × D true) (D v) then π2 else π1) |}.
Next Obligation. apply product_limit. apply product_universal. Defined.

Program Definition ProductLimits {C : Cat} `{HP : !HasProduct C}
  : HasLimitsOfShape C PairShape := {| hasLimit := ProductDiagramLimit |}.

Program Definition PairLimitsProduct {C : Cat} `{HL : !HasLimitsOfShape C PairShape}
  : HasProduct C :=
  {| Prod X Y := lim ⟨X, Y⟩D
   ; π1 X Y := πlim[⟨X, Y⟩D] false
   ; π2 X Y := πlim[⟨X, Y⟩D] true |}.
Next Obligation.
  exact (limit_product (πlim[⟨X, Y⟩D]) (limit_universal ⟨X, Y⟩D)).
Defined.

(** Preservation follows from the general limit theorem. *)
Definition right_adjoint_preserves_product {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {X Y P : @Ob D} {p : Hom P X} {q : Hom P Y}
    (HP : is_product X Y P p q)
  : is_product (G X) (G Y) (G P) (fmap G p) (fmap G q) :=
  limit_product (MapCone G (PairCone p q))
    (right_adjoint_preserves_limit A (product_limit (PairCone p q) HP)).
