From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.Functor.ExponentialComparison
  Cat.Limit.Exponential
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Exponential
  Instance.Set.Terminal
  Instance.Set.Initial
  Instance.Bool.Group.
From CatsTests.gluing Require Import
  Gluing.
From CatsTests.category Require Import
  ProductPreservation.

(** * Weak Composition of Comparison Maps

    Three independent category profiles check the weak hypotheses. Reader
    composition computes at two distinct Boolean environments. An empty
    constant functor keeps its noninvertible exponential comparison. *)

(** ** Increasing Category Bounds

    Keep all native object, hom, equality and auxiliary law levels
    separate; introduce choices only when a comparison uses them. *)

Section IndependentComposition.
Universes oc hc ec lc od hd ed ld oe he ee le.
Constraint hc < ec, ec < oc, oc < lc, lc < hd.
Constraint hd < ed, ed < od, od < ld, ld < he.
Constraint he < ee, ee < oe, oe < le.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context {E : Cat@{oe he ee le le}} (F : Fct C D) (G : Fct D E).
Context {PC : HasProduct C}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** Candidate preservation does not choose target products. *)

Definition independent_product_cone {X Y P : C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
  : is_product (F X) (F Y) (F P) (fmap F p) (fmap F q)
  := preserved_product_cone F preservesF HP.

Context {PD : HasProduct D}.
Context (preservesG : ∀ X Y : D,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).

(** The composite candidate still needs no target product choice. *)

Definition independent_product_comp (X Y : C)
  : is_product ((G ∘F F) X) ((G ∘F F) Y)
      ((G ∘F F) ((X × Y)%ob))
      (fmap (G ∘F F) π1) (fmap (G ∘F F) π2)
  := preserved_product_comp F G preservesF preservesG X Y.

Context {PE : HasProduct E}.
Context (preservesGF : ∀ X Y : C,
    is_product ((G ∘F F) X) ((G ∘F F) Y)
      ((G ∘F F) ((X × Y)%ob))
      (fmap (G ∘F F) π1) (fmap (G ∘F F) π2)).

(** An independently supplied composite witness is permitted. *)

Definition independent_product_inv_comp (X Y : C)
  : preserved_product_inv (G ∘F F) preservesGF X Y ≈
      fmap G (preserved_product_inv F preservesF X Y) ∘
        preserved_product_inv G preservesG (F X) (F Y)
  := preserved_product_inv_comp F G preservesF preservesG preservesGF X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.
Context {EE : HasExponential PE}.

(** Exponential composition requires neither terminal nor inverse data. *)

Definition independent_exp_comp (X Y : C)
  : exp_cmp (G ∘F F) preservesGF X Y ≈
      exp_cmp G preservesG (F X) (F Y) ∘
        fmap G (exp_cmp F preservesF X Y)
  := exp_cmp_comp F G
      preservesF preservesG preservesGF X Y.

End IndependentComposition.

(** ** Reversed Category Bounds

    Keep all native object, hom, equality and auxiliary law levels
    separate; introduce choices only when a comparison uses them. *)

Section ReversedComposition.
Universes oc hc ec lc od hd ed ld oe he ee le.
Constraint ee < he, he < oe, oe < le, le < ed.
Constraint ed < hd, hd < od, od < ld, ld < ec.
Constraint ec < hc, hc < oc, oc < lc.
Context {C : Cat@{oc hc ec lc lc}} {D : Cat@{od hd ed ld ld}}.
Context {E : Cat@{oe he ee le le}} (F : Fct C D) (G : Fct D E).
Context {PC : HasProduct C}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** Candidate preservation does not choose target products. *)

Definition reversed_product_cone {X Y P : C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
  : is_product (F X) (F Y) (F P) (fmap F p) (fmap F q)
  := preserved_product_cone F preservesF HP.

Context {PD : HasProduct D}.
Context (preservesG : ∀ X Y : D,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).

(** The composite candidate still needs no target product choice. *)

Definition reversed_product_comp (X Y : C)
  : is_product ((G ∘F F) X) ((G ∘F F) Y)
      ((G ∘F F) ((X × Y)%ob))
      (fmap (G ∘F F) π1) (fmap (G ∘F F) π2)
  := preserved_product_comp F G preservesF preservesG X Y.

Context {PE : HasProduct E}.
Context (preservesGF : ∀ X Y : C,
    is_product ((G ∘F F) X) ((G ∘F F) Y)
      ((G ∘F F) ((X × Y)%ob))
      (fmap (G ∘F F) π1) (fmap (G ∘F F) π2)).

(** An independently supplied composite witness is permitted. *)

Definition reversed_product_inv_comp (X Y : C)
  : preserved_product_inv (G ∘F F) preservesGF X Y ≈
      fmap G (preserved_product_inv F preservesF X Y) ∘
        preserved_product_inv G preservesG (F X) (F Y)
  := preserved_product_inv_comp F G preservesF preservesG preservesGF X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.
Context {EE : HasExponential PE}.

(** Exponential composition requires neither terminal nor inverse data. *)

Definition reversed_exp_comp (X Y : C)
  : exp_cmp (G ∘F F) preservesGF X Y ≈
      exp_cmp G preservesG (F X) (F Y) ∘
        fmap G (exp_cmp F preservesF X Y)
  := exp_cmp_comp F G
      preservesF preservesG preservesGF X Y.

End ReversedComposition.

(** Function exponentials require a separate choice. *)

Fail Definition automatic_composition_exponentials
  : @HasExponential SetCat SetCat_HasProduct
  := ltac:(typeclasses eauto).

(** ** Two Reader Environments

    Use the standard setoid products and locally chosen exponentials. Reuse the
    general right-adjoint preservation theorem for exponentiation, rather
    than another pointwise product universal-property proof. *)

Section ReaderComposition.
Local Instance composition_exponentials
  : HasExponential SetCat_HasProduct
  := SetCat_HasExponential.

(** Each stage reads one Boolean environment. *)

Definition CompositionReaderF
  : Fct SetCat SetCat
  := (-^ BoolS).

(** Product preservation is inherited from the product-exponential adjunction. *)

Definition composition_reader_products (X Y : SetC)
  : is_product (CompositionReaderF X) (CompositionReaderF Y)
      (CompositionReaderF ((X × Y)%ob))
      (fmap CompositionReaderF π1) (fmap CompositionReaderF π2)
  := exp_preserves_product BoolS product_universal.

(** Compose the supplied cones, without a CCC-functor input. *)

Definition composition_readers_products (X Y : SetC)
  : is_product (CompositionReaderF (CompositionReaderF X))
      (CompositionReaderF (CompositionReaderF Y))
      (CompositionReaderF (CompositionReaderF ((X × Y)%ob)))
      (fmap CompositionReaderF (fmap CompositionReaderF π1))
      (fmap CompositionReaderF (fmap CompositionReaderF π2))
  := preserved_product_comp CompositionReaderF CompositionReaderF
      composition_reader_products composition_reader_products X Y.

(** The product equation uses the constructed composite witness. *)

Definition composition_readers_product_law (X Y : SetC)
  : preserved_product_inv
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      X Y ≈ fmap CompositionReaderF
        (preserved_product_inv CompositionReaderF composition_reader_products
          X Y) ∘ preserved_product_inv CompositionReaderF
        composition_reader_products (CompositionReaderF X) (CompositionReaderF Y)
  := preserved_product_inv_comp CompositionReaderF CompositionReaderF
      composition_reader_products composition_reader_products
      composition_readers_products X Y.

(** Exponential factorization uses the same supplied comparisons. *)

Definition composition_readers_exp_law (X Y : SetC)
  : exp_cmp
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      X Y ≈ exp_cmp CompositionReaderF
        composition_reader_products (CompositionReaderF X)
          (CompositionReaderF Y) ∘ fmap CompositionReaderF
        (exp_cmp CompositionReaderF
          composition_reader_products X Y)
  := exp_cmp_comp CompositionReaderF
      CompositionReaderF composition_reader_products
      composition_reader_products composition_readers_products X Y.

(** A genuinely environment-dependent family returns a tagged value. *)

Program Definition composition_reader_functions
  : BoolS →r (BoolS →S (TaggedGluingS →S TaggedGluingS))
  :=
  {|func outer := {|func inner :=
      {|func x := (fst x, xorb outer (xorb inner (snd x)))|}|}
  |}.
Next Obligation. intros [n b] [m c] [H t]. exact (H, negb t). Defined.
Next Obligation. intros b c H [n t]. exact (eq_refl, true). Defined.
Next Obligation. intros b c H inner [n t]. exact (eq_refl, false). Defined.

(** Its two environments also provide a nonconstant argument family. *)

Program Definition composition_reader_argument
  : BoolS →r (BoolS →S TaggedGluingS)
  :=
  {|func outer :=
      {|func inner := (3%nat, xorb outer inner)
      ; func_proper b c H := (eq_refl, false)
      |}
  ; func_proper b c H inner := (eq_refl, true)
  |}.

(** The direct comparison retains both environment positions. *)

Example composition_reader_direct_computes
  : exp_cmp
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS composition_reader_functions
      composition_reader_argument true false = (3%nat, false).
Proof. reflexivity. Defined.

(** Factoring the comparison computes the same result at those positions. *)

Example composition_reader_factored_computes
  : (exp_cmp CompositionReaderF
      composition_reader_products (CompositionReaderF TaggedGluingS)
        (CompositionReaderF TaggedGluingS) ∘
      fmap CompositionReaderF (exp_cmp
        CompositionReaderF composition_reader_products
        TaggedGluingS TaggedGluingS)) composition_reader_functions
      composition_reader_argument true false = (3%nat, false).
Proof. reflexivity. Defined.

(** Both computations genuinely depend on the supplied environment family. *)

Program Definition composition_reader_constant_argument
  : BoolS →r (BoolS →S TaggedGluingS)
  :=
  {|func outer :=
      {|func inner := (3%nat, false)
      ; func_proper b c H := (eq_refl, true)
      |}
  ; func_proper b c H inner := (eq_refl, false)
  |}.

(** Changing the argument exposes the two environment effects. *)

Example composition_reader_environment_computes
  : exp_cmp
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS composition_reader_functions
      composition_reader_constant_argument true false = (3%nat, true).
Proof. reflexivity. Defined.

(** Pairing through the composite retains its original universal mediator. *)

Example composition_reader_product_computes
  : preserved_product_inv
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS
      (composition_reader_argument, composition_reader_constant_argument)
      true false = ((3%nat, true), (3%nat, false)).
Proof. reflexivity. Defined.

(** The factored inverse product map has the same native data computation. *)

Example composition_reader_product_factored_computes
  : (fmap CompositionReaderF
      (preserved_product_inv CompositionReaderF composition_reader_products
        TaggedGluingS TaggedGluingS) ∘
      preserved_product_inv CompositionReaderF composition_reader_products
        (CompositionReaderF TaggedGluingS) (CompositionReaderF TaggedGluingS))
      (composition_reader_argument, composition_reader_constant_argument)
      true false = ((3%nat, true), (3%nat, false)).
Proof. reflexivity. Defined.

(** The constant identity family has different native tags. *)

Program Definition composition_reader_identity_functions
  : BoolS →r (BoolS →S (TaggedGluingS →S TaggedGluingS))
  :=
  {|func outer :=
      {|func inner := id_resp
      ; func_proper b c H x := (eq_refl, false)
      |}
  ; func_proper b c H inner x := (eq_refl, true)
  |}.

(** The composite comparison respects Type-valued function equality,
    without identifying its function or law records. *)

Example composition_reader_function_equality
  : exp_cmp
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS composition_reader_functions ≈S
      exp_cmp
        (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
        TaggedGluingS TaggedGluingS composition_reader_identity_functions.
Proof.
  apply func_proper. intros outer inner [n b]. exact (eq_refl, false).
Defined.

(** Specified equality retains observable differences of representatives. *)

Example composition_reader_distinct_tags_compute
  : exp_cmp
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS composition_reader_identity_functions
      composition_reader_argument true false = (3%nat, true).
Proof. reflexivity. Defined.

End ReaderComposition.

(** ** An Independent Composite Witness and a Noninvertible Comparison

    Use the empty constant functor after identity. The composite witness
    is supplied directly, instead of using [preserved_product_comp].
    Composition still applies although terminal and exponential
    preservation are both impossible for this functor. *)

Section EmptyComposition.
Local Existing Instance SetCat_HasExponential.

(** Directly supplied preservation witnesses need not be equal records. *)

Definition composition_empty_product_law (X Y : SetC)
  : preserved_product_inv (ConstF SetCat EmptyS ∘F (@IdF SetCat))
      empty_constant_preserves_products X Y ≈
      fmap (ConstF SetCat EmptyS)
        (preserved_product_inv (@IdF SetCat) (λ X Y, product_universal) X Y) ∘
      preserved_product_inv (ConstF SetCat EmptyS)
        empty_constant_preserves_products X Y
  := preserved_product_inv_comp (@IdF SetCat) (ConstF SetCat EmptyS)
      (λ X Y, product_universal) empty_constant_preserves_products
      empty_constant_preserves_products X Y.

(** No inverse exponential comparison enters the composition theorem. *)

Definition composition_empty_exp_law (X Y : SetC)
  : exp_cmp
      (ConstF SetCat EmptyS ∘F (@IdF SetCat))
      empty_constant_preserves_products X Y ≈
      exp_cmp (ConstF SetCat EmptyS)
        empty_constant_preserves_products X Y ∘
      fmap (ConstF SetCat EmptyS)
        (exp_cmp (@IdF SetCat)
          (λ X Y, product_universal) X Y)
  := exp_cmp_comp (@IdF SetCat)
      (ConstF SetCat EmptyS) (λ X Y, product_universal)
      empty_constant_preserves_products empty_constant_preserves_products X Y.

(** An inverse would construct an element of the empty carrier. *)

Definition composition_comparison_not_iso
  : is_iso (exp_cmp
      (ConstF SetCat EmptyS ∘F (@IdF SetCat))
      empty_constant_preserves_products BoolS BoolS) → Empty_set
  := empty_constant_comparison_not_iso.

(** Binary-product composition also supplies no terminal preservation. *)

Definition composition_not_terminal
  : is_terminal ((ConstF SetCat EmptyS ∘F (@IdF SetCat)) UnitS) → Empty_set
  := empty_constant_not_terminal.

End EmptyComposition.
