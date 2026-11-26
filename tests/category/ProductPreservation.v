From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC.Functor
  Cat.Functor.ExponentialComparison
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Exponential
  Instance.Set.Terminal
  Instance.Set.Initial
  Instance.Bool.Group.

(** * Weak Comparison Interfaces and Computation

    Strictly separate native hom and equality levels in both orders.
    Concrete comparisons retain their original mediators, while a functor
    to the empty setoid shows why terminal and exponential preservation
    must not be inferred from binary-product preservation. *)

(** ** Equality above Hom

    Use [ed < hd < hc < ec < o < l] with only binary-product preservation.
    No terminal structures occur in the comparison signatures. *)

Section LargeEquality.
Universes ed hd hc ec o l.
Constraint ed < hd, hd < hc, hc < ec, ec < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ X Y : @Ob C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** The inverse product comparison keeps the target native hom level. *)

Definition product_comparison_large_equality (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := preserved_product_inv F preserves X Y.

(** Exponential comparison accepts the same independent equality bounds. *)

Definition exp_cmp_large_equality (X Y : @Ob C)
  : Hom (F ((Y ^ X)%ob)) (F Y ^ F X)
  := exp_cmp F preserves X Y.

End LargeEquality.

(** ** Equality below Hom

    Reverse the order to [ec < hd < ed < hc < o < l]. The same weak
    comparisons accept a larger native source hom and smaller equality. *)

Section SmallEquality.
Universes ec hd ed hc o l.
Constraint ec < hd, hd < ed, ed < hc, hc < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ X Y : @Ob C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** Product comparison does not identify the native levels. *)

Definition product_comparison_small_equality (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := preserved_product_inv F preserves X Y.

(** Exponential comparison retains the reverse strict separation. *)

Definition exp_cmp_small_equality (X Y : @Ob C)
  : Hom (F ((Y ^ X)%ob)) (F Y ^ F X)
  := exp_cmp F preserves X Y.

End SmallEquality.

(** ** Explicit Setoid Choices and Native Computation

    Use standard products and enable exponentials locally. Identity comparisons compute
    without evaluating universal-property proofs. The old cartesian API
    continues to use the very same product mediator. *)

Section SetoidComparisons.
Local Existing Instance SetCat_HasExponential.

(** The weak inverse product comparison computes both input components. *)

Example preserved_product_computes
  : preserved_product_inv (@IdF SetCat)
      (λ X Y, product_universal) BoolS BoolS (true, false) = (true, false).
Proof. reflexivity. Defined.

(** The weak exponential comparison evaluates its original function. *)

Example preserved_exp_computes
  : exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) BoolS BoolS id_resp true = true.
Proof. reflexivity. Defined.

(** The existing API keeps native computation after the proof extraction. *)

Example cartesian_product_computes
  : @fct_product_inv SetCat SetCat IdF SetCat_HasTerminal
      SetCat_HasProduct SetCat_HasProduct
      (IdF_IsCartF SetCat SetCat_HasTerminal SetCat_HasProduct)
      BoolS BoolS (false, true) = (false, true).
Proof. reflexivity. Defined.

(** The existing exponential comparison has the same transparent data. *)

Example cartesian_exp_computes
  : @fct_exp_cmp SetCat SetCat IdF
      SetCat_HasTerminal SetCat_HasProduct SetCat_HasExponential
      SetCat_HasProduct SetCat_HasExponential
      (IdF_IsCartF SetCat SetCat_HasTerminal SetCat_HasProduct)
      BoolS BoolS id_resp false = false.
Proof. reflexivity. Defined.

(** ** Binary Products without Terminal or Exponential Preservation

    The constant functor at the empty setoid preserves binary products.
    Its image terminal is empty, and its exponential comparison has empty
    domain and an inhabited codomain, so it cannot be invertible. *)

(** The empty setoid, with identity legs, is its own binary product. *)

Definition empty_constant_preserves_products (X Y : SetC)
  : is_product ((ConstF SetCat EmptyS) X) ((ConstF SetCat EmptyS) Y)
      ((ConstF SetCat EmptyS) ((X × Y)%ob))
      (fmap (ConstF SetCat EmptyS) π1) (fmap (ConstF SetCat EmptyS) π2).
Proof.
  intros Z f g. exists f. split.
  - split; intros z; exact tt.
  - intros k H z. exact tt.
Defined.

(** A map from the terminal setoid into the image terminal is impossible. *)

Definition empty_constant_not_terminal (H : is_terminal EmptyS)
  : Empty_set
  := (H UnitS).1 tt.

(** The weak exponential comparison is available for this functor. *)

Definition empty_constant_exp_cmp
  : EmptyS →r (EmptyS →S EmptyS)
  := exp_cmp (ConstF SetCat EmptyS)
      empty_constant_preserves_products BoolS BoolS.

(** Its inverse would send the identity function to an empty element. *)

Definition empty_constant_comparison_not_iso
    (H : is_iso (C := SetCat) empty_constant_exp_cmp)
  : Empty_set
  := H.1 id_resp.

End SetoidComparisons.
