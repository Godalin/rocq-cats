From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Pullback
  Cat.Morphism
  Topos.Sub.
From Cats Require Import
  Instance.Set.Core
  Cat.Coproduct.Core
  Cat.Coequalizer
  Cat.Equalizer
  Cat.Pushout
  Instance.Set.Limit
  Instance.Set.Colimit
  Instance.Set.Pushout.

From Cats Require Import
  Instance.Set.Simplicial.Vertex.Coskeletal.

(** Coskeletal vertex-nerve structures also require explicit enabling. *)

Section VertexCoskeletalChoice.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C).

Fail Definition unchosen_vertex_coskeletal
  : Nᵥ(T) ⦂ Cosk[2%nat]
  := ltac:(typeclasses eauto).
End VertexCoskeletalChoice.

(** Coproducts, equalizers, coequalizers and pushouts require explicit choices. *)

Fail Definition unchosen_set_coproducts
  : HasCoproduct SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_coequalizers
  : HasCoequalizer SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_equalizers
  : HasEqualizer SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_pushouts
  : HasPushout SetCat
  := ltac:(typeclasses eauto).

Section Pullback.
Context {C : Cat} `{HP : !HasPullback C}.
Context {X Y Z P : @Ob C} (f : Hom X Z) (g : Hom Y Z).
Context (p1 : Hom P X) (p2 : Hom P Y).

(** A pair of legs alone must not supply a mediator for a noncommuting cone. *)

Fail Definition mediator_without_commutativity : Hom P (Pb f g) :=
  @pb C HP X Y Z f g P p1 p2.

End Pullback.

Section Classifier.
Context {C : Cat} `{HT : !HasTerminal C} `{HC : !HasSubObjClassifier HT}.
Context {X Y : @Ob C} (m : X ↣ Y).

(** The selected square is not evidence that an arbitrary candidate classifies m. *)

Fail Definition arbitrary_candidate_unique (c : Hom Y Ω) : c ≈ χ m :=
  that (classifier_char_unique (m := m)) c (this (classifier_char_unique (m := m))).

End Classifier.

From Cats Require Import
  Cat.Monoidal.Cartesian
  Instance.Set.Monoid.

(** The standard terminal object and products induce the cartesian tensor on setoids. *)

Definition inferred_set_monoidal
  : HasMonoidal SetCat
  := ltac:(typeclasses eauto).

(** The same tensor supplies the underlying binoidal actions. *)

Definition inferred_set_binoidal
  : HasBinoidal SetCat
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Monoidal.Premonoidal.

(** ** Independent Premonoidal Choices

    A fixed tensor may have only an associator or only unitors. Inheriting
    one package must not select the other or a complete extension. *)

Section AssociatorChoice.
Context {C : Cat} `{BC : !HasBinoidal C} `{AC : !@HasTensorAssoc C BC}.

Fail Definition unchosen_unitors
  : @HasTensorUnitors C BC
  := ltac:(typeclasses eauto).

End AssociatorChoice.

(** Unit choices alone likewise select no associator. *)

Section UnitorChoice.
Context {C : Cat} `{BC : !HasBinoidal C} `{UC : !@HasTensorUnitors C BC}.

Fail Definition unchosen_associator
  : @HasTensorAssoc C BC
  := ltac:(typeclasses eauto).

End UnitorChoice.

From Cats Require Import
  Cat.Monoidal.Constant.

(** Bundling the underlying functor must not register a chosen lax structure
    for the concrete model. Clients choose identity or constant explicitly. *)

Fail Definition unchosen_set_lax_monoidal
  : @LaxMonoidalFct _ _ SetCartMonoidal SetCartMonoidal
  := ltac:(typeclasses eauto).

(** Adding invertible comparisons must not choose a monoidal functor. *)

Fail Definition unchosen_set_monoidal_fct
  : @MonoidalFct _ _ SetCartMonoidal SetCartMonoidal
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Applicative.Core.

(** Importing the theory must not select an Applicative on the model. *)

Fail Definition unchosen_set_applicative
  : @Applicative SetCat SetCat_HasTerminal SetCat_HasProduct
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Functor.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Fixed
  Instance.Set.Sieve.Matching.

(** Canonical projections infer the specified set equality from the carrier
    types, without an explicit set annotation or comparison of law fields. *)

Definition inferred_family_map_equality {X : SetC} {A B : FamS X}
    (f g : A →Fam B)
  : Type
  := f ≈S g.

Definition inferred_matching_equality {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    (P : Fct (C^op) SetCat) (a b : SieveMatching g P)
  : Type
  := a ≈S b.

From Cats Require Import
  Cat.FreeObject.Adjunction.

(** The general theorem does not install a chosen free-object structure. *)

Fail Definition unchosen_free_objects
  : HasFreeObj (@IdF SetCat)
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.CCC.Functor
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC.Core
  Instance.Set.CCC.

(** Bundled preservation does not select concrete cartesian or CCC functors
    merely by import. *)

Fail Definition unchosen_set_cartesian_fct
  : @CartFct SetCat SetCat SetCat_HasTerminal SetCat_HasProduct
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_ccc_fct
  : CCCFct SetCat_CCC SetCat_CCC
  := ltac:(typeclasses eauto).

(** Cartesian inheritance needs no chosen structures in the target. *)

Section BundledCartesianInference.
Context {C D : Cat} {TC : HasTerminal C} {PC : HasProduct C}
    (F : @CartFct C D TC PC).

Definition inferred_cartesian_preservation
  : IsCartF F TC PC
  := ltac:(typeclasses eauto).
End BundledCartesianInference.

(** A supplied CCC bundle supports both inherited interfaces and the
    existing curry theorem through its single functor coercion chain. *)

Section BundledCCCInference.
Context {C D : CCC} (F : CCCFct C D).

(** Packing a fixed functor preserves both of the supplied witnesses
    by conversion, including the dependency between them. *)

Example packed_ccc_cart_witness (G : Fct C D) (H : @IsCCCF C D G)
  : isCartF (CCCFctToCartFct (CCCFctOfIsCCCF G H)) = IsCCCF_isCartF H
  := eq_refl.

Example packed_ccc_exp_witness (G : Fct C D) (H : @IsCCCF C D G)
  : CCCFct_preservesExp (CCCFctOfIsCCCF G H) = IsCCCF_preservesExp H
  := eq_refl.

Definition inferred_ccc_preservation
  : @IsCCCF C D F
  := ltac:(typeclasses eauto).
Definition inferred_ccc_cartesian_preservation
  : IsCartF F (hasTerminal C) (hasProduct C)
  := ltac:(typeclasses eauto).
Definition bundled_fct_curry {X Y Z : @Ob C} (f : Hom (Z × X) Y)
  : fct_exp_cmp F X Y ∘ fmap F (ƛ f) ≈
      ƛ (fmap F f ∘ fct_product_inv F Z X)
  := fct_curry F f.
End BundledCCCInference.
