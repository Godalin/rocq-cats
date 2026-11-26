From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Topos.Sub
  Topos.Nat
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Exponential
  Cat.CCC.Core
  Topos.ETCS
  Instance.Set.CCC.

(** * Explicit Structured Categories

    Complete bundles expose one category and its selected constructions.
    Setoids have standard terminal and product instances. Bundles over the
    same category retain their own computational witnesses. *)

Fail Definition unchosen_cartesian_category
  : CartCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_closed_category
  : CCC
  := ltac:(typeclasses eauto).
Fail Definition unchosen_topos
  : Topos
  := ltac:(typeclasses eauto).
Fail Definition unchosen_etcs
  : ETCS
  := ltac:(typeclasses eauto).
Definition inferred_set_terminal
  : HasTerminal SetCat
  := ltac:(typeclasses eauto).
Definition inferred_set_products
  : HasProduct SetCat
  := ltac:(typeclasses eauto).
Example inferred_set_terminal_is_standard
  : inferred_set_terminal = SetCat_HasTerminal
  := eq_refl.
Example inferred_set_products_are_standard
  : inferred_set_products = SetCat_HasProduct
  := eq_refl.

Fail Definition unchosen_set_exponentials
  : HasExponential SetCat_HasProduct
  := ltac:(typeclasses eauto).

(** ** Inherited Operations

    A supplied ETCS bundle must support ordinary mathematical notation and
    weaker chosen-structure interfaces through its single parent chain. *)

Section InheritedOperations.
Context (C : ETCS).

Definition inherited_object_view (x : C)
  : @Ob (C : Cat)
  := x.
Definition inherited_curry {X Y Z : C} (f : Hom (Z × X) Y)
  : Hom Z (Y ^ X)
  := ƛ f.
Definition inherited_classifier
  : HasSubObjClassifier (hasTerminal C)
  := ltac:(typeclasses eauto).
Definition inherited_natural_numbers
  : HasNaturalNumbersObj (hasTerminal C)
  := ltac:(typeclasses eauto).

End InheritedOperations.

(** ** Separate Choices on One Category

    The indiscrete Boolean setoid is terminal. Two valid terminal choices
    select different literal constant maps, while sharing SetCat, products
    and exponentials. Reading a bundle must retain that distinction. *)

Module SeparateChoices.

Program Definition TokenS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv _ _ := unit
  |}.
Next Obligation. split; red; intros; exact tt. Defined.

Program Definition TokenTerminal (b : bool)
  : HasTerminal SetCat
  :=
  {|Term := TokenS
  |}.
Next Obligation.
  intro X. assert (h : X →r TokenS).
  { unshelve notypeclasses refine {|func := _
                                  |}.
    - exact (λ _, b).
    - intros x y p. exact tt. }
  exists h. split; [exact I |]. intros f _ x. exact tt.
Defined.

Program Definition TokenCCC (b : bool)
  : CCC
  := MakeCCC SetCat (TokenTerminal b) SetCat_HasProduct
      SetCat_HasExponential.

Example false_terminal_computes
  : @term (TokenCCC false) (hasTerminal (TokenCCC false)) UnitS tt = false.
Proof. reflexivity. Qed.

Example true_terminal_computes
  : @term (TokenCCC true) (hasTerminal (TokenCCC true)) UnitS tt = true.
Proof. reflexivity. Qed.

Example explicit_product_pair_computes
  : @pair (TokenCCC true) (hasProduct (TokenCCC true))
      TokenS TokenS TokenS id_resp id_resp false = (false, false).
Proof. reflexivity. Qed.

End SeparateChoices.
