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
From CatsGluingTests Require Import
  Gluing.
From CatsCategoryTests Require Import
  ProductPreservation.

(** * Gluing Exponential Interfaces and Computational Witnesses

    Keep native hom/equality bounds separate in both strict orders. The
    setoid example retains observable equality witnesses and checks the
    pullback-valued transpose, its base component and evaluation. *)

(** * 粘合指数接口与可计算见证

    按两个严格次序分离原有 Hom／相等界。广集例子保留可观测的相等见证，并
    检查取值于拉回的转置、其基分量及求值。 *)

(** ** Only the Particular Pullbacks, with Larger Equality

    For [ed < hd < hc < ec < o < l], supply just the comparison pullback
    family. The target has no terminal choice or all-pullback structure. *)

(** ** 相等较大时只提供特定拉回

    对 [ed < hd < hc < ec < o < l]，只给出比较拉回族。目标没有终对象选择
    或全部拉回结构。 *)

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

(** 较弱的选定族接口接受严格独立的层级。 *)

Definition gluing_exp_large_equality
  : HasExponential (Gluing_HasProduct F preserves)
  := Gluing_HasExponential F preserves pullbacks.

(** Adding only the base terminal yields the complete CCC structure. *)

(** 只加入基终对象即可得到完整 CCC 结构。 *)

Definition gluing_ccc_large_equality `{TC : !HasTerminal C}
  : CCC
  := Gluing_CCC F preserves pullbacks.

End LargeEquality.

(** ** The All-Pullback Wrapper, with Smaller Equality

    Reverse to [ec < hd < ed < hc < o < l]. Target pullbacks give the
    sufficient wrapper without identifying native hom and equality bounds. *)

(** ** 相等较小时的全部拉回包装

    反转为 [ec < hd < ed < hc < o < l]。目标拉回给出充分条件包装，而不合并
    原有 Hom 与相等界。 *)

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

(** 便捷包装保持反向分离。 *)

Definition gluing_exp_small_equality
  : HasExponential (Gluing_HasProduct F preserves)
  := GluingPullback_HasExponential F preserves.

(** The CCC wrapper needs no target terminal object. *)

(** CCC 包装不需要目标终对象。 *)

Definition gluing_ccc_small_equality `{TC : !HasTerminal C}
  : CCC
  := GluingPullback_CCC F preserves.

End SmallEquality.

(** ** Transparent Computation with Nontrivial Setoid Equality

    Explicitly enable the setoid model's products, exponentials and
    pullbacks only here. Reuse the tagged setoid from the gluing tests:
    equality ignores tags and retains a Boolean witness. *)

(** ** 非平凡广集相等下的透明计算

    仅在此显式启用广集模型的积、指数和拉回。复用粘合测试中的带标签广集：
    相等忽略标签，并保留一个布尔见证。 *)

Section SetoidExponentials.
Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasExponential.
Local Existing Instance SetCat_HasPullback.

(** Select precisely the already constructed gluing products. *)

(** 恰好选择已经构造的粘合积。 *)

Local Instance gluing_products
  : HasProduct (Gluing (@IdF SetCat))
  := Gluing_HasProduct IdF (λ X Y, product_universal).

(** Select exponentials relative to that same product choice. *)

(** 相对于同一积选择选取指数。 *)

Local Instance gluing_exponentials
  : HasExponential gluing_products
  := GluingPullback_HasExponential IdF (λ X Y, product_universal).

(** The example ignores its second input and changes the first tag. *)

(** 例子忽略第二输入，并改变第一输入的标签。 *)

Definition tagged_gluing_function
  : (@Hom (Gluing (@IdF SetCat)))
      ((TaggedGluingObj × TaggedGluingObj)%ob) TaggedGluingObj
  := tagged_gluing_toggle ∘ π1.

(** Its left transpose stores a respectful function in the pullback. *)

(** 左转置在拉回中存储一个保相等函数。 *)

Example tagged_gluing_curry_left_computes
  : (comma_left (ƛ tagged_gluing_function) (3, false)).1 (4, true) =
      (3, true).
Proof. reflexivity. Defined.

(** The base transpose is the original base curry, with no pullback search. *)

(** 基转置就是原基柯里化，无须搜索拉回。 *)

Example tagged_gluing_curry_right_computes
  : comma_right (ƛ tagged_gluing_function) (5, true) (4, false) =
      (5, false).
Proof. reflexivity. Defined.

(** The pullback's second coordinate also keeps the base function. *)

(** 拉回的第二坐标也保留基函数。 *)

Example tagged_gluing_curry_base_computes
  : (comma_left (ƛ tagged_gluing_function) (6, false)).2.1 (9, true) =
      (6, true).
Proof. reflexivity. Defined.

(** Apply the abstracted function to the same argument in both components. *)

(** 在两个分量中将抽象函数应用于同一个参数。 *)

Definition tagged_gluing_application
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedGluingObj
  := eval ∘ ⟨ƛ tagged_gluing_function, id⟩.

(** Left evaluation projects the stored function and computes directly. *)

(** 左求值投影出存储的函数并直接计算。 *)

Example tagged_gluing_eval_left_computes
  : comma_left tagged_gluing_application (7, false) = (7, true).
Proof. reflexivity. Defined.

(** Right evaluation remains the selected base evaluation. *)

(** 右求值仍是选定的基求值。 *)

Example tagged_gluing_eval_right_computes
  : comma_right tagged_gluing_application (8, true) = (8, false).
Proof. reflexivity. Defined.

(** Transposition respects the specified equality even when the underlying
    tagged functions differ natively. No square-proof equality is needed. *)

(** 即使底层带标签函数原生不同，转置仍保持指定相等，不需要方形证明相等。 *)

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

(** 观察拉回元素保留的布尔见证，它与两个存储函数坐标的等价分开。 *)

Definition tagged_gluing_curry_witness_retained
  : bool
  := snd ((comma_left (ƛ tagged_gluing_function) (2, false)).2.2
      (1%nat, true)).

(** The constant-empty functor from the comparison tests preserves binary
    products but not terminals or exponentials. Its gluing is nevertheless
    a CCC under the present sufficient pullback hypotheses. *)

(** 比较测试中的常空函子保持二元积，但不保持终对象或指数。在当前的充分
    拉回条件下，其粘合仍然是 CCC。 *)

Definition empty_constant_gluing_ccc
  : CCC
  := GluingPullback_CCC (ConstF SetCat EmptyS)
      empty_constant_preserves_products (TC := SetCat_HasTerminal).

End SetoidExponentials.
