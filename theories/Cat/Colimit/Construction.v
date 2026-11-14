From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Arrow.Core
  Cat.Coequalizer
  Cat.Limit.Construction.
From Cats Require Export
  Cat.Coproduct.Indexed.

(** * Colimits from Coproducts and Coequalizers

    The original opposite construction uses only coproducts over the
    objects and over the sources of arrows. Reversed arrows index the latter,
    so [arrow_cod] there is the source in the original shape. *)

(** * 从余积与余等化子构造余极限

    原反构造只使用对象余积和箭头源对象余积；后者由反箭头索引，因而其中的
    [arrow_cod] 就是原形状中的源。 *)

(** The object-index family of the diagram. *)

(** 图式的对象索引族。 *)

Definition CodiagramObj {J C : Cat} (D : Fct J C) (j : @Ob J)
  : @Ob C
  := D j.

(** Index source objects by reversed arrows, retaining all dependent
    endpoint data without transporting equality of records. *)

(** 用反箭头索引源对象，保留全部依赖端点数据，无需沿记录相等运输。 *)

Definition CodiagramSources {J C : Cat} (D : Fct J C)
    (a : ArrowOb (J^op))
  : @Ob C
  := D (arrow_cod a).

(** ** Colimit Constraints from Coproducts

    Fix a diagram [D] and chosen coproducts of its objects and arrow sources.
    Form the two constraint arrows and use a coequalizer to obtain the colimit
    property. *)

(** ** 用余积表达余极限约束

    固定图式 [D] 及其对象和箭头源的选定余积，构造两条约束箭头，再用余等化子获得余极限泛性质。 *)

Section CoproductConstraints.
Context {J C : Cat} (D : Fct J C).
Context `{HO : !HasColimit C (DiscreteF (CodiagramObj D))}.
Context `{HA : !HasColimit C (DiscreteF (CodiagramSources D))}.

(** Keep the selected object coproduct as the original opposite product. *)

(** 将选定对象余积保留为原反积。 *)

Local Definition codiagram_objects_product
  : HasLimit (C^op) (@DiscreteF (C^op) _ (CodiagramObj D))
  := @IndexedCoproductOpProduct C _ (CodiagramObj D) HO.

(** Keep the selected source coproduct as the original opposite product. *)

(** 将选定源对象余积保留为原反积。 *)

Local Definition codiagram_sources_product
  : HasLimit (C^op) (@DiscreteF (C^op) _ (CodiagramSources D))
  := @IndexedCoproductOpProduct C _ (CodiagramSources D) HA.

(** For a reversed arrow [a], inject its original source into the object
    coproduct. This is the original opposite target constraint. *)

(** 对反箭头 [a]，将其原源注入对象余积；这就是原反目标约束。 *)

Definition codiagram_coproduct_source
  : Hom ∐[CodiagramSources D] ∐[CodiagramObj D]
  := @diagram_product_target (J^op) (C^op) (D^opF)
      codiagram_objects_product codiagram_sources_product.

(** Apply the diagram arrow, then inject its original target. This is the
    original opposite source constraint. *)

(** 先应用图式箭头，再注入其原目标；这就是原反源约束。 *)

Definition codiagram_coproduct_target
  : Hom ∐[CodiagramSources D] ∐[CodiagramObj D]
  := @diagram_product_source (J^op) (C^op) (D^opF)
      codiagram_objects_product codiagram_sources_product.

(** Coequalizing target and source constraints gives a cocone through the
    original opposite equalizer cone. *)

(** 将目标与源约束余等化，通过原反等化子锥得到余锥。 *)

Program Definition CoproductsCoequalizerCocone {E : @Ob C}
    (e : Hom ∐[CodiagramObj D] E)
    (H : e ∘ codiagram_coproduct_target ≈ e ∘ codiagram_coproduct_source)
  : D ⇒∇ E.
Proof.
  refine {|op_cone := _|}.
  exact (@ProductsEqualizerCone (J^op) (C^op) (D^opF)
    codiagram_objects_product codiagram_sources_product E e H).
Defined.

(** A candidate coequalizer has the colimit property by the original
    product/equalizer limit theorem, with no new mediator uniqueness proof. *)

(** 候选余等化子由原积／等化子极限定理得到余极限性质，不另证中介唯一性。 *)

Definition coproducts_coequalizer_colimit {E : @Ob C}
    (e : Hom ∐[CodiagramObj D] E)
    (H : e ∘ codiagram_coproduct_target ≈ e ∘ codiagram_coproduct_source)
    (HE : is_coequalizer codiagram_coproduct_target
      codiagram_coproduct_source E e)
  : is_colimit (CoproductsCoequalizerCocone e H)
  := @products_equalizer_limit (J^op) (C^op) (D^opF)
      codiagram_objects_product codiagram_sources_product E e H HE.

End CoproductConstraints.

(** Two ordinary discrete coproduct choices supply the original opposite
    product/equalizer construction. For an arrow [i → j], its parallel maps
    are the injection at [i] and the injection at [j] after its diagram map.
    No universal property is reproved. *)

(** 两个通常离散余积选择给出原反积／等化子构造。对箭头 [i → j]，两条平行映射
    分别是 [i] 处注入及图式映射后接 [j] 处注入；不重证泛性质。 *)

Program Definition CoproductsCoequalizerColimit {J C : Cat}
    (D : Fct J C)
    `{HO : !HasColimit C (DiscreteF (CodiagramObj D))}
    `{HA : !HasColimit C (DiscreteF (CodiagramSources D))}
    `{HE : !HasCoequalizer C}
  : HasColimit C D
  :=
  {|hasOpLimit := @ProductsEqualizerLimit (J^op) (C^op) (D^opF)
      (@IndexedCoproductOpProduct C _ (CodiagramObj D) HO)
      (@IndexedCoproductOpProduct C _ (CodiagramSources D) HA)
      (@hasOpEqualizer C HE)
  |}.

(** Uniform choices give all colimits of the shape. Size assumptions are
    limited to these two explicit discrete index types. *)

(** 一致选择给出整个形状的全部余极限；大小假设仅限于这两个显式离散索引类型。 *)

Program Definition IndexedCoproductsCoequalizerColimits {J C : Cat}
    `{HO : !HasColimitsOfShape C (DiscreteCat (@Ob J))}
    `{HA : !HasColimitsOfShape C (DiscreteCat (ArrowOb (J^op)))}
    `{HE : !HasCoequalizer C}
  : HasColimitsOfShape C J
  :=
  {|hasOpLimits := @IndexedProductsEqualizerLimits (J^op) (C^op)
      (@DiscreteColimitsOpLimits C _ HO)
      (@DiscreteColimitsOpLimits C _ HA) (@hasOpEqualizer C HE)
  |}.
