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

(** * 弱比较自然性

    严格配置分离两个原生范畴边界。具体计算改变参数类型及可观察的结果标签；
    不可逆自然边界及不可逆指数比较检查没有暗中加入更强保持性。 *)

(** ** Independent Category Bounds

    Keep object, hom, equality and auxiliary law levels distinct. The
    product equation precedes all exponential hypotheses, and no terminal
    or inverse structure is supplied. *)

(** ** 独立范畴边界

    分离对象、Hom、相等及辅助律层级。积方程在指数假设之前给出，不提供
    终对象或逆结构。 *)

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

(** 积边界相容性保留其较弱假设。 *)

Definition independent_product_boundary (X Y : C)
  : α ((X × Y)%ob) ∘ preserved_product_inv F preservesF X Y ≈
      preserved_product_inv G preservesG X Y ∘ (α X × α Y)
  := preserved_product_inv_boundary F G preservesF preservesG α X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.

(** Distinct argument/result objects test both variances. *)

(** 不同参数／结果对象检查两个变型。 *)

Definition independent_exp_natural {X X' Y Y' : C}
    (u : Hom X' X) (v : Hom Y Y')
  : exp_cmp F preservesF X' Y' ∘ fmap F (v ^ u) ≈
      (fmap F v ^ fmap F u) ∘
        exp_cmp F preservesF X Y
  := exp_cmp_natural F preservesF u v.

(** The mixed endpoint is [G Y ^ F X], without inverse components. *)

(** 混合端点为[G Y ^ F X]，不提供逆分量。 *)

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

(** ** 反向范畴边界

    分离对象、Hom、相等及辅助律层级。积方程在指数假设之前给出，不提供
    终对象或逆结构。 *)

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

(** 积边界相容性保留其较弱假设。 *)

Definition reversed_product_boundary (X Y : C)
  : α ((X × Y)%ob) ∘ preserved_product_inv F preservesF X Y ≈
      preserved_product_inv G preservesG X Y ∘ (α X × α Y)
  := preserved_product_inv_boundary F G preservesF preservesG α X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.

(** Distinct argument/result objects test both variances. *)

(** 不同参数／结果对象检查两个变型。 *)

Definition reversed_exp_natural {X X' Y Y' : C}
    (u : Hom X' X) (v : Hom Y Y')
  : exp_cmp F preservesF X' Y' ∘ fmap F (v ^ u) ≈
      (fmap F v ^ fmap F u) ∘
        exp_cmp F preservesF X Y
  := exp_cmp_natural F preservesF u v.

(** The mixed endpoint is [G Y ^ F X], without inverse components. *)

(** 混合端点为[G Y ^ F X]，不提供逆分量。 *)

Definition reversed_exp_boundary (X Y : C)
  : (α Y ^ (id[F X])) ∘
      exp_cmp F preservesF X Y ≈
      ((id[G Y]) ^ α X) ∘
        exp_cmp G preservesG X Y ∘
        α ((Y ^ X)%ob)
  := exp_cmp_boundary F G preservesF preservesG α X Y.

End ReversedNaturality.

(** Respectful-function exponentials require a separate choice. *)

(** 保相等函数指数须另外选定。 *)

Fail Definition automatic_naturality_exponentials
  : @HasExponential SetCat SetCat_HasProduct
  := ltac:(typeclasses eauto).

(** ** Computation and Noninvertible Boundaries

    Use the standard setoid products and locally chosen exponentials. The source
    argument changes from a tagged setoid to Boolean. The result action
    changes an ignored tag, retaining an actual computational difference. *)

(** ** 计算与不可逆边界

    使用标准广集积和局部选定的指数。来源参数从标签广集变为布尔，结果作用改变被
    忽略的标签，同时保留实际计算差异。 *)

Section ConcreteNaturality.
Local Instance naturality_exponentials
  : HasExponential SetCat_HasProduct
  := SetCat_HasExponential.

(** A Boolean argument determines the ignored tag of a fixed-number value. *)

(** 布尔参数决定固定数值的被忽略标签。 *)

Program Definition comparison_argument
  : BoolS →r TaggedGluingS
  :=
  {|func b := (3, b)
  ; func_proper x y h := (eq_refl, true)
  |}.

(** The ordinary natural unit collapse needs no inverse components. *)

(** 普通自然单位塌缩不要求逆分量。 *)

Program Definition ComparisonUnitN
  : (@IdF SetCat) ⇒ ConstF SetCat UnitS
  :=
  {|nt X := @term SetCat SetCat_HasTerminal X
  ; nat_naturality X Y f x := tt
  |}.

(** Reuse the earlier concrete proof that this component is not invertible. *)

(** 复用已有的具体分量不可逆证明。 *)

Definition comparison_unit_not_iso
  : is_iso (ComparisonUnitN TaggedGluingS) → Empty_set
  := product_boundary_not_iso.

(** Product compatibility applies to the actual noninvertible boundary. *)

(** 积相容性适用于此实际不可逆边界。 *)

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

(** 结果作用与参数作用具有不同端点类型。 *)

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

(** 边界律使用单位结果／布尔参数的混合指数。 *)

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

(** 左侧逆积比较在塌缩之前计算。 *)

Example comparison_product_input_computes
  : preserved_product_inv (@IdF SetCat)
      (λ X Y, product_universal) TaggedGluingS BoolS ((3, false), true) =
      ((3, false), true).
Proof. reflexivity. Defined.

(** Product-boundary transport computes the expected unit value. *)

(** 积边界运输计算为预期单位值。 *)

Example comparison_product_boundary_computes
  : (preserved_product_inv (ConstF SetCat UnitS) unit_model_product
      TaggedGluingS BoolS ∘
      (ComparisonUnitN TaggedGluingS × ComparisonUnitN BoolS))
      ((3, false), true) = tt.
Proof. reflexivity. Defined.

(** Changing the result after the Boolean argument gives an actual tag flip. *)

(** 改变结果在布尔参数之后给出实际标签翻转。 *)

Example comparison_natural_left_computes
  : (exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) BoolS TaggedGluingS ∘
      (gluing_toggle ^ comparison_argument)) id_resp false = (3, true).
Proof. reflexivity. Defined.

(** The other path retains its independent input tag as well. *)

(** 另一条路径也保留其独立输入标签。 *)

Example comparison_natural_right_computes
  : ((gluing_toggle ^ comparison_argument) ∘
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS TaggedGluingS)
      id_resp true = (3, false).
Proof. reflexivity. Defined.

(** The mixed exponential's left boundary path evaluates at a Boolean. *)

(** 混合指数的左边界路径在布尔处求值。 *)

Example comparison_boundary_left_computes
  : ((ComparisonUnitN TaggedGluingS ^ (id[BoolS])) ∘
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) BoolS TaggedGluingS)
      comparison_argument true = tt.
Proof. reflexivity. Defined.

(** The right path first collapses the represented object, then restricts. *)

(** 右路径先塌缩表示对象，再限制参数。 *)

Example comparison_boundary_right_computes
  : (((id[UnitS]) ^ ComparisonUnitN BoolS) ∘
      exp_cmp (ConstF SetCat UnitS)
        unit_model_product BoolS TaggedGluingS ∘
      ComparisonUnitN ((TaggedGluingS ^ BoolS)%ob))
      comparison_argument false = tt.
Proof. reflexivity. Defined.

(** The existing comparison respects nontrivial specified function equality. *)

(** 既有比较保持非平凡指定函数相等。 *)

Example comparison_respects_tagged_functions
  : exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) TaggedGluingS TaggedGluingS gluing_toggle ≈S
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS TaggedGluingS id_resp.
Proof.
  apply func_proper. intros [n b]. exact (eq_refl, true).
Defined.

(** Specified function equality does not erase different native tags. *)

(** 指定函数相等不会擦除原生不同的标签。 *)

Example comparison_distinct_functions_compute
  : (exp_cmp (@IdF SetCat)
      (λ X Y, product_universal) TaggedGluingS TaggedGluingS
      gluing_toggle (3, false),
      exp_cmp (@IdF SetCat)
        (λ X Y, product_universal) TaggedGluingS TaggedGluingS
        id_resp (3, false)) = ((3, true), (3, false)).
Proof. reflexivity. Defined.

(** These weak naturality equations do not make the comparison invertible. *)

(** 这些弱自然性方程不使比较可逆。 *)

Definition naturality_does_not_imply_exp_preservation
  : is_iso (exp_cmp (ConstF SetCat EmptyS)
      empty_constant_preserves_products BoolS BoolS) → Empty_set
  := empty_constant_comparison_not_iso.

End ConcreteNaturality.
