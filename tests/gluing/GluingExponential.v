From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Pullback
  Cat.Gluing.CCC
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Initial
  Instance.Set.Product
  Instance.Set.Exponential
  Instance.Set.Pullback.
From CatsTests.gluing Require Import
  Gluing.
From CatsTests.category Require Import
  ProductPreservation.

(** * Gluing Exponential Interfaces and Computational Witnesses

    Keep native hom/equality bounds separate in both strict orders. The
    setoid example retains observable equality witnesses and checks the
    pullback-valued transpose, its base component and evaluation. *)

(** ** Only the Particular Pullbacks, with Larger Equality

    For [ed < hd < hc < ec < o < l], supply just the comparison pullback
    family. The target has no terminal choice or all-pullback structure. *)

Section LargeEquality.
Universes ed hd hc ec o l.
Constraint ed < hd, hd < hc, hc < ec, ec < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ A B : @Ob C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (pullbacks : ∀ X Y : @Ob (Gluing F),
    ∃ E : @Ob D,
    ∃ p : Hom E (comma_left_ob Y ^ comma_left_ob X),
    ∃ q : Hom E (F ((comma_right_ob Y ^ comma_right_ob X)%ob)),
      is_pullback (gluing_exp_result F X Y)
        (gluing_exp_base F preserves X Y) E p q).

(** The weaker selected-family interface accepts strict independent levels. *)

Definition gluing_exp_large_equality
  : HasExponential (Gluing_HasProduct F preserves)
  := Gluing_HasExponential F preserves pullbacks.

(** Adding only the base terminal yields the complete CCC structure. *)

Definition gluing_ccc_large_equality `{TC : !HasTerminal C}
  : CCC
  := Gluing_CCC F preserves pullbacks.

End LargeEquality.

(** ** The All-Pullback Wrapper, with Smaller Equality

    Reverse to [ec < hd < ed < hc < o < l]. Target pullbacks give the
    sufficient wrapper without identifying native hom and equality bounds. *)

Section SmallEquality.
Universes ec hd ed hc o l.
Constraint ec < hd, hd < ed, ed < hc, hc < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}
    `{HPb : !HasPullback D}.
Context (preserves : ∀ A B : @Ob C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).

(** The convenience wrapper keeps the reverse separation. *)

Definition gluing_exp_small_equality
  : HasExponential (Gluing_HasProduct F preserves)
  := GluingPullback_HasExponential F preserves.

(** The CCC wrapper needs no target terminal object. *)

Definition gluing_ccc_small_equality `{TC : !HasTerminal C}
  : CCC
  := GluingPullback_CCC F preserves.

End SmallEquality.

(** ** Transparent Computation with Nontrivial Setoid Equality

    Use the setoid model's standard products and explicitly enable exponentials and
    pullbacks only here. Reuse the tagged setoid from the gluing tests:
    equality ignores tags and retains a Boolean witness. *)

Section SetoidExponentials.
Local Existing Instance SetCat_HasExponential.
Local Existing Instance SetCat_HasPullback.

(** Select precisely the already constructed gluing products. *)

Local Instance gluing_products
  : HasProduct (Gluing (@IdF SetCat))
  := Gluing_HasProduct IdF (λ X Y, product_universal).

(** Select exponentials relative to that same product choice. *)

Local Instance gluing_exponentials
  : HasExponential gluing_products
  := GluingPullback_HasExponential IdF (λ X Y, product_universal).

(** The example ignores its second input and changes the first tag. *)

Definition tagged_gluing_function
  : (@Hom (Gluing (@IdF SetCat)))
      ((TaggedGluingObj × TaggedGluingObj)%ob) TaggedGluingObj
  := tagged_gluing_toggle ∘ π1.

(** Its left transpose stores a respectful function in the pullback. *)

Example tagged_gluing_curry_left_computes
  : (comma_left (ƛ tagged_gluing_function) (3, false)).1 (4, true) =
      (3, true).
Proof. reflexivity. Defined.

(** The base transpose is the original base curry, with no pullback search. *)

Example tagged_gluing_curry_right_computes
  : comma_right (ƛ tagged_gluing_function) (5, true) (4, false) =
      (5, false).
Proof. reflexivity. Defined.

(** The pullback's second coordinate also keeps the base function. *)

Example tagged_gluing_curry_base_computes
  : (comma_left (ƛ tagged_gluing_function) (6, false)).2.1 (9, true) =
      (6, true).
Proof. reflexivity. Defined.

(** Apply the abstracted function to the same argument in both components. *)

Definition tagged_gluing_application
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedGluingObj
  := eval ∘ ⟨ƛ tagged_gluing_function, id⟩.

(** Left evaluation projects the stored function and computes directly. *)

Example tagged_gluing_eval_left_computes
  : comma_left tagged_gluing_application (7, false) = (7, true).
Proof. reflexivity. Defined.

(** Right evaluation remains the selected base evaluation. *)

Example tagged_gluing_eval_right_computes
  : comma_right tagged_gluing_application (8, true) = (8, false).
Proof. reflexivity. Defined.

(** Transposition respects the specified equality even when the underlying
    tagged functions differ natively. No square-proof equality is needed. *)

Example tagged_gluing_curry_respects
  : ƛ tagged_gluing_function ≈ ƛ (π1 : (@Hom (Gluing (@IdF SetCat)))
      ((TaggedGluingObj × TaggedGluingObj)%ob) TaggedGluingObj).
Proof.
  apply exp_curry_proper.
  unfold tagged_gluing_function.
  rewrite tagged_gluing_toggle_equal, comp_id_l. reflexivity.
Defined.

(** Observe the Boolean witness retained by the pullback element, separate
    from the equivalence of its two stored function coordinates. *)

Definition tagged_gluing_curry_witness_retained
  : bool
  := snd ((comma_left (ƛ tagged_gluing_function) (2, false)).2.2
      (1%nat, true)).

(** The constant-empty functor from the comparison tests preserves binary
    products but not terminals or exponentials. Its gluing is nevertheless
    a CCC under the present sufficient pullback hypotheses. *)

Definition empty_constant_gluing_ccc
  : CCC
  := GluingPullback_CCC (ConstF SetCat EmptyS)
      empty_constant_preserves_products (TC := SetCat_HasTerminal).

End SetoidExponentials.
