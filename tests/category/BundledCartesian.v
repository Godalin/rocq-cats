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
    Imports must not select a model, and bundles over the same category
    must retain their own computational witnesses. *)

(** * 显式的带结构范畴

    完整结构包暴露唯一范畴及其选定构造。导入不得默认选择模型，
    同一范畴上的不同结构包必须保留各自的计算见证。 *)

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
Fail Definition unchosen_set_terminal
  : HasTerminal SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_products
  : HasProduct SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_exponentials
  : HasExponential SetCat_HasProduct
  := ltac:(typeclasses eauto).

(** ** Inherited Operations

    A supplied ETCS bundle must support ordinary mathematical notation and
    weaker chosen-structure interfaces through its single parent chain. *)

(** ** 继承运算

    给定 ETCS 结构包须通过唯一父链支持普通数学记号及较弱的选择结构接口。 *)

Section InheritedOperations.
Context (C : ETCS).

Definition inherited_object_view (x : C)
  : @Ob (C : Cat)
  := x.
Definition inherited_curry {X Y Z : C} (f : Hom (Z × X) Y)
  : Hom Z (Y ^ X)
  := ƛ f.
Definition inherited_classifier
  : HasSubObjClassifier C (hasTerminal C)
  := ltac:(typeclasses eauto).
Definition inherited_natural_numbers
  : HasNaturalNumbersObj C (hasTerminal C)
  := ltac:(typeclasses eauto).

End InheritedOperations.

(** ** Separate Choices on One Category

    The indiscrete Boolean setoid is terminal. Two valid terminal choices
    select different literal constant maps, while sharing SetCat, products
    and exponentials. Reading a bundle must retain that distinction. *)

(** ** 同一范畴上的不同选择

    非离散布尔广集是终对象。两份合法终对象选择给出不同的字面常值映射，
    但共享 SetCat、积及指数。读取结构包必须保留这种区别。 *)

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
  :=
  {|CCCToCartCat :=
    {|CartCatToCat := SetCat
    ; hasTerminal := TokenTerminal b
    ; hasProduct := SetCat_HasProduct
    |}
  ; hasExponential := SetCat_HasExponential
  |}.

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
