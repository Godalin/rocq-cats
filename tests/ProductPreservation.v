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

(** * 弱比较接口与计算

    按两个次序严格分离原有 Hom 与相等层级。具体比较保留原中介；取值于空
    广集的函子则说明不能从二元积保持性推出终对象或指数保持性。 *)

(** ** Equality above Hom

    Use [ed < hd < hc < ec < o < l] with only binary-product preservation.
    No terminal structures occur in the comparison signatures. *)

(** ** 相等高于 Hom

    使用 [ed < hd < hc < ec < o < l]，只提供二元积保持性。比较的类型
    中不出现终对象结构。 *)

Section LargeEquality.
Universes ed hd hc ec o l.
Constraint ed < hd, hd < hc, hc < ec, ec < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ X Y : @Ob C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** The inverse product comparison keeps the target native hom level. *)

(** 逆积比较保持目标原有的 Hom 层级。 *)

Definition product_comparison_large_equality (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := preserved_product_inv F preserves X Y.

(** Exponential comparison accepts the same independent equality bounds. *)

(** 指数比较接受同样独立的相等界。 *)

Definition exponential_comparison_large_equality (X Y : @Ob C)
  : Hom (F ((Y ^ X)%ob)) (F Y ^ F X)
  := preserved_exponential_comparison F preserves X Y.

End LargeEquality.

(** ** Equality below Hom

    Reverse the order to [ec < hd < ed < hc < o < l]. The same weak
    comparisons accept a larger native source hom and smaller equality. *)

(** ** 相等低于 Hom

    将次序反转为 [ec < hd < ed < hc < o < l]。相同的弱比较接受较大的
    原有来源 Hom 和较小的相等界。 *)

Section SmallEquality.
Universes ec hd ed hc o l.
Constraint ec < hd, hd < ed, ed < hc, hc < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ X Y : @Ob C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** Product comparison does not identify the native levels. *)

(** 积比较不合并原有层级。 *)

Definition product_comparison_small_equality (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := preserved_product_inv F preserves X Y.

(** Exponential comparison retains the reverse strict separation. *)

(** 指数比较保留反向的严格分离。 *)

Definition exponential_comparison_small_equality (X Y : @Ob C)
  : Hom (F ((Y ^ X)%ob)) (F Y ^ F X)
  := preserved_exponential_comparison F preserves X Y.

End SmallEquality.

(** ** Explicit Setoid Choices and Native Computation

    Enable products and exponentials locally. Identity comparisons compute
    without evaluating universal-property proofs. The old cartesian API
    continues to use the very same product mediator. *)

(** ** 显式广集选择与原生计算

    局部启用积和指数。恒等比较的计算无需对泛性质证明求值；原有笛卡尔接口
    继续使用完全相同的积中介。 *)

Section SetoidComparisons.
Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasExponential.

(** The weak inverse product comparison computes both input components. *)

(** 弱逆积比较计算两个输入分量。 *)

Example preserved_product_computes
  : preserved_product_inv (@IdF SetCat)
      (λ X Y, product_universal) BoolS BoolS (true, false) = (true, false).
Proof. reflexivity. Defined.

(** The weak exponential comparison evaluates its original function. *)

(** 弱指数比较对原函数求值。 *)

Example preserved_exponential_computes
  : preserved_exponential_comparison (@IdF SetCat)
      (λ X Y, product_universal) BoolS BoolS id_resp true = true.
Proof. reflexivity. Defined.

(** The existing API keeps native computation after the proof extraction. *)

(** 提取证明后，已有接口仍保持原生计算。 *)

Example cartesian_product_computes
  : @functor_product_inv SetCat SetCat IdF SetCat_HasTerminal
      SetCat_HasProduct SetCat_HasProduct
      (IdF_IsCartF SetCat SetCat_HasTerminal SetCat_HasProduct)
      BoolS BoolS (false, true) = (false, true).
Proof. reflexivity. Defined.

(** The existing exponential comparison has the same transparent data. *)

(** 原指数比较保留同样透明的数据。 *)

Example cartesian_exponential_computes
  : @functor_exponential_comparison SetCat SetCat IdF
      SetCat_HasTerminal SetCat_HasProduct SetCat_HasExponential
      SetCat_HasProduct SetCat_HasExponential
      (IdF_IsCartF SetCat SetCat_HasTerminal SetCat_HasProduct)
      BoolS BoolS id_resp false = false.
Proof. reflexivity. Defined.

(** ** Binary Products without Terminal or Exponential Preservation

    The constant functor at the empty setoid preserves binary products.
    Its image terminal is empty, and its exponential comparison has empty
    domain and an inhabited codomain, so it cannot be invertible. *)

(** ** 不保持终对象或指数的二元积保持性

    取值于空广集的常值函子保持二元积。其终对象的像为空；指数比较的定义域
    为空而陪域有元素，因此不可逆。 *)

(** The empty setoid, with identity legs, is its own binary product. *)

(** 以恒等为锥腿，空广集是自身与自身的二元积。 *)

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

(** 从终广集到终对象的像的映射不可能存在。 *)

Definition empty_constant_not_terminal (H : is_terminal EmptyS)
  : Empty_set
  := (H UnitS).1 tt.

(** The weak exponential comparison is available for this functor. *)

(** 对此函子，弱指数比较仍然存在。 *)

Definition empty_constant_exponential_comparison
  : EmptyS →r (EmptyS →S EmptyS)
  := preserved_exponential_comparison (ConstF SetCat EmptyS)
      empty_constant_preserves_products BoolS BoolS.

(** Its inverse would send the identity function to an empty element. *)

(** 它的逆将把恒等函数送到一个空载体的元素。 *)

Definition empty_constant_comparison_not_iso
    (H : is_iso (C := SetCat) empty_constant_exponential_comparison)
  : Empty_set
  := H.1 id_resp.

End SetoidComparisons.
