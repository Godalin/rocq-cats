From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Cat.CCC.Core
  Cat.CCC.Functor
  Cat.CCC.Category
  Instance.Set.Core.
From CatsTests.category Require Import
  BundledCartesian.

(** * The Category of CCC Bundles

    Exercise ordinary categorical notation, setoid rewriting, and forgetting
    structured functors. Two bundles over the same category retain different
    choices while admitting an actual structured arrow between them. *)

(** ** Ordinary Categorical Clients

    Fix three objects of CCCCat and arrows between them. The canonical
    category must infer the intended homs and rewriting through composition. *)

Section CategoricalClients.
Context (C D E : @Ob CCCCat) (F F' : Hom C D) (G : Hom D E).

Definition structured_composite
  : Hom C E
  := G ∘ F.
Definition underlying_composite
  : Fct C E
  := fmap CCCForgetF structured_composite.

Example structured_composition_rewrites (H : F ≈ F')
  : G ∘ F ≈ G ∘ F'.
Proof. rewrite H. reflexivity. Qed.

End CategoricalClients.

(** ** Distinct Choices and Concrete Computation

    Reuse the two terminal-map witnesses from BundledCartesian. Products
    and exponentials agree definitionally, so the existing identity
    preservation fields give a CCC arrow without equating the bundles. *)

Module ChangedChoices.
Import SeparateChoices.

Program Definition ChoiceChangePreservation
  : @IsCCCF (TokenCCC false) (TokenCCC true) IdF
  :=
  {|IsCCCF_isCartF := @IsCCCF_isCartF (TokenCCC false) (TokenCCC false) IdF
      (IdF_IsCCCF (TokenCCC false))
  ; IsCCCF_preservesExp :=
      {|fct_exp := fct_exp
          (PreservesExp := IsCCCF_preservesExp (IdF_IsCCCF (TokenCCC false)))|}
  |}.

Definition ChoiceChange
  : (@Hom CCCCat) (TokenCCC false) (TokenCCC true)
  := CCCFctOfIsCCCF
    (C := TokenCCC false) (D := TokenCCC true) IdF ChoiceChangePreservation.

Example forget_choice_change_computes
  : fmap (fmap CCCForgetF ChoiceChange)
      (@Cats.Cat.Core.id (TokenCCC false) TokenS) false = false.
Proof. reflexivity. Qed.

Example composite_forget_computes
  : fmap (fmap CCCForgetF
      (@Cats.Cat.Core.comp CCCCat _ _ _ (@Cats.Cat.Core.id CCCCat (TokenCCC true)) ChoiceChange))
      (@Cats.Cat.Core.id (TokenCCC false) TokenS) true = true.
Proof. reflexivity. Qed.

End ChangedChoices.

(** ** Larger Auxiliary Proof Bounds

    The underlying functor retains both auxiliary proof levels of a CCC
    functor even when they strictly exceed the category law level. *)

Section ProofBounds.
Universes o h p l m n.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < m.
Constraint m < n.
Constraint n < o.
Context (C : CCC@{o h p l l}) (D : CCC@{o h p l m})
    (F : CCCFct@{m m n o h p l o h p l l} C D).

Definition larger_proof_underlying
  : Fct@{o h p l m n o h p l} C D
  := F.

End ProofBounds.
