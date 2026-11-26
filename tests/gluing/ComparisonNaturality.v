From Cats Require Import
  Cat.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.Functor.ComparisonNaturality
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Exponential
  Instance.Set.Terminal
  Instance.Set.Initial
  Instance.Bool.Group.
From CatsTests.gluing Require Import
  Gluing
  GluingChangeProduct.
From CatsTests.category Require Import
  ProductPreservation.

(** * Weak Comparison Naturality

    Strict profiles separate both native category boundaries. Concrete
    computations change an argument type and observable result tags. A
    noninvertible natural boundary and a noninvertible exponential
    comparison check that no stronger preservation is silently assumed. *)

(** ** Independent Category Bounds

    Keep object, hom, equality and auxiliary law levels distinct. The
    product equation precedes all exponential hypotheses, and no terminal
    or inverse structure is supplied. *)

Section IndependentNaturality.
Universes oc hc ec lc od hd ed ld.
Constraint hc < ec, ec < oc, oc < lc, lc < hd, hd < ed, ed < od, od < ld.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F G : Fct C D).
Context {PC : HasProduct C} {PD : HasProduct D}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).
Context (preservesG : ∀ X Y : C,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).
Context (α : F ⇒ G).

(** Product-boundary compatibility keeps its weaker hypotheses. *)

Definition independent_product_boundary (X Y : C)
  : α ((X × Y)%ob) ∘ preserved_product_inv F preservesF X Y ≈
      preserved_product_inv G preservesG X Y ∘ (α X × α Y)
  := preserved_product_inv_boundary F G preservesF preservesG α X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.

(** Distinct argument/result objects test both variances. *)

Definition independent_exp_natural {X X' Y Y' : C}
    (u : Hom X' X) (v : Hom Y Y')
  : exp_cmp F preservesF X' Y' ∘ fmap F (v ^ u) ≈
      (fmap F v ^ fmap F u) ∘
        exp_cmp F preservesF X Y
  := exp_cmp_natural F preservesF u v.

(** The mixed endpoint is [G Y ^ F X], without inverse components. *)

Definition independent_exp_boundary (X Y : C)
  : (α Y ^ (id[F X])) ∘
      exp_cmp F preservesF X Y ≈
      ((id[G Y]) ^ α X) ∘
        exp_cmp G preservesG X Y ∘
        α ((Y ^ X)%ob)
  := exp_cmp_boundary F G preservesF preservesG α X Y.

End IndependentNaturality.

(** ** Reversed Category Bounds

    Keep object, hom, equality and auxiliary law levels distinct. The
    product equation precedes all exponential hypotheses, and no terminal
    or inverse structure is supplied. *)

Section ReversedNaturality.
Universes oc hc ec lc od hd ed ld.
Constraint ed < hd, hd < od, od < ld, ld < ec, ec < hc, hc < oc, oc < lc.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context (F G : Fct C D).
Context {PC : HasProduct C} {PD : HasProduct D}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).
Context (preservesG : ∀ X Y : C,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).
Context (α : F ⇒ G).

(** Product-boundary compatibility keeps its weaker hypotheses. *)

Definition reversed_product_boundary (X Y : C)
  : α ((X × Y)%ob) ∘ preserved_product_inv F preservesF X Y ≈
      preserved_product_inv G preservesG X Y ∘ (α X × α Y)
  := preserved_product_inv_boundary F G preservesF preservesG α X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.

(** Distinct argument/result objects test both variances. *)

Definition reversed_exp_natural {X X' Y Y' : C}
    (u : Hom X' X) (v : Hom Y Y')
  : exp_cmp F preservesF X' Y' ∘ fmap F (v ^ u) ≈
      (fmap F v ^ fmap F u) ∘
        exp_cmp F preservesF X Y
  := exp_cmp_natural F preservesF u v.

(** The mixed endpoint is [G Y ^ F X], without inverse components. *)

Definition reversed_exp_boundary (X Y : C)
  : (α Y ^ (id[F X])) ∘
      exp_cmp F preservesF X Y ≈
      ((id[G Y]) ^ α X) ∘
        exp_cmp G preservesG X Y ∘
        α ((Y ^ X)%ob)
  := exp_cmp_boundary F G preservesF preservesG α X Y.

End ReversedNaturality.

(** Respectful-function exponentials require a separate choice. *)

Fail Definition automatic_naturality_exponentials
  : @HasExponential SetCat SetCat_HasProduct
  := ltac:(typeclasses eauto).

(** ** Computation and Noninvertible Boundaries

    Use the standard setoid products and locally chosen exponentials. The source
    argument changes from a tagged setoid to Boolean. The result action
    changes an ignored tag, retaining an actual computational difference. *)

Section ConcreteNaturality.
Local Instance naturality_exponentials
  : HasExponential SetCat_HasProduct
  := SetCat_HasExponential.

(** A Boolean argument determines the ignored tag of a fixed-number value. *)

Program Definition comparison_argument
  : BoolS →r TaggedGluingS
  :=
  {|func b := (3, b)
  ; func_proper x y h := (eq_refl, true)
  |}.

(** The ordinary natural unit collapse needs no inverse components. *)

Program Definition ComparisonUnitN
  : (@IdF SetCat) ⇒ ConstF SetCat UnitS
  :=
  {|nt X := @term SetCat SetCat_HasTerminal X
  ; nat_naturality X Y f x := tt
  |}.

(** Reuse the earlier concrete proof that this component is not invertible. *)

Definition comparison_unit_not_iso
  : is_iso (ComparisonUnitN TaggedGluingS) → Empty_set
  := product_boundary_not_iso.

(** Product compatibility applies to the actual noninvertible boundary. *)

Definition comparison_unit_product_law
  : ComparisonUnitN ((TaggedGluingS × BoolS)%ob) ∘
      preserved_product_inv (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS BoolS ≈
      preserved_product_inv (ConstF SetCat UnitS) unit_model_product
        TaggedGluingS BoolS ∘ (ComparisonUnitN TaggedGluingS ×
        ComparisonUnitN BoolS)
  := preserved_product_inv_boundary (@IdF SetCat) (ConstF SetCat UnitS)
      (λ X Y, product_universal) unit_model_product ComparisonUnitN _ _.

(** The result and argument actions have different endpoint types. *)

Definition comparison_argument_result_law
  : exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) BoolS TaggedGluingS ∘
      (gluing_toggle ^ comparison_argument) ≈
      (gluing_toggle ^ comparison_argument) ∘
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS TaggedGluingS
  := exp_cmp_natural (@IdF SetCat)
      (λ X Y, product_universal) comparison_argument gluing_toggle.

(** The boundary law uses a mixed unit-result/Boolean-argument exponential. *)

Definition comparison_unit_exp_law
  : (ComparisonUnitN TaggedGluingS ^ (id[BoolS])) ∘
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) BoolS TaggedGluingS ≈
      ((id[UnitS]) ^ ComparisonUnitN BoolS) ∘
        exp_cmp (ConstF SetCat UnitS)
          unit_model_product BoolS TaggedGluingS ∘
        ComparisonUnitN ((TaggedGluingS ^ BoolS)%ob)
  := exp_cmp_boundary (@IdF SetCat) (ConstF SetCat UnitS)
      (λ X Y, product_universal) unit_model_product ComparisonUnitN _ _.

(** The inverse product comparison on the left computes before collapse. *)

Example comparison_product_input_computes
  : preserved_product_inv (@IdF SetCat)
      (λ X Y, product_universal) TaggedGluingS BoolS ((3, false), true) =
      ((3, false), true).
Proof. reflexivity. Defined.

(** Product-boundary transport computes the expected unit value. *)

Example comparison_product_boundary_computes
  : (preserved_product_inv (ConstF SetCat UnitS) unit_model_product
      TaggedGluingS BoolS ∘
      (ComparisonUnitN TaggedGluingS × ComparisonUnitN BoolS))
      ((3, false), true) = tt.
Proof. reflexivity. Defined.

(** Changing the result after the Boolean argument gives an actual tag flip. *)

Example comparison_natural_left_computes
  : (exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) BoolS TaggedGluingS ∘
      (gluing_toggle ^ comparison_argument)) id_resp false = (3, true).
Proof. reflexivity. Defined.

(** The other path retains its independent input tag as well. *)

Example comparison_natural_right_computes
  : ((gluing_toggle ^ comparison_argument) ∘
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS TaggedGluingS)
      id_resp true = (3, false).
Proof. reflexivity. Defined.

(** The mixed exponential's left boundary path evaluates at a Boolean. *)

Example comparison_boundary_left_computes
  : ((ComparisonUnitN TaggedGluingS ^ (id[BoolS])) ∘
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) BoolS TaggedGluingS)
      comparison_argument true = tt.
Proof. reflexivity. Defined.

(** The right path first collapses the represented object, then restricts. *)

Example comparison_boundary_right_computes
  : (((id[UnitS]) ^ ComparisonUnitN BoolS) ∘
      exp_cmp (ConstF SetCat UnitS)
        unit_model_product BoolS TaggedGluingS ∘
      ComparisonUnitN ((TaggedGluingS ^ BoolS)%ob))
      comparison_argument false = tt.
Proof. reflexivity. Defined.

(** The existing comparison respects nontrivial specified function equality. *)

Example comparison_respects_tagged_functions
  : exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) TaggedGluingS TaggedGluingS gluing_toggle ≈S
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS TaggedGluingS id_resp.
Proof.
  apply func_proper. intros [n b]. exact (eq_refl, true).
Defined.

(** Specified function equality does not erase different native tags. *)

Example comparison_distinct_functions_compute
  : (exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) TaggedGluingS TaggedGluingS
      gluing_toggle (3, false),
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS TaggedGluingS
        id_resp (3, false)) = ((3, true), (3, false)).
Proof. reflexivity. Defined.

(** These weak naturality equations do not make the comparison invertible. *)

Definition naturality_does_not_imply_exp_preservation
  : is_iso (exp_cmp (ConstF SetCat EmptyS)
      empty_constant_preserves_products BoolS BoolS) → Empty_set
  := empty_constant_comparison_not_iso.

End ConcreteNaturality.
