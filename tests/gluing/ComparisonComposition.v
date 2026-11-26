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

(** * 比较映射的弱复合

    三个独立范畴配置检查弱假设；Reader 复合在两个不同布尔环境处计算。
    常空函子仍具有不可逆指数比较。 *)

(** ** Increasing Category Bounds

    Keep all native object, hom, equality and auxiliary law levels
    separate; introduce choices only when a comparison uses them. *)

(** ** 递增的范畴界

    分离所有原生对象、Hom、相等及辅助律层级，只在比较需要时引入选择。 *)

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

(** 候选保持性不选择目标积。 *)

Definition independent_product_cone {X Y P : C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
  : is_product (F X) (F Y) (F P) (fmap F p) (fmap F q)
  := preserved_product_cone F preservesF HP.

Context {PD : HasProduct D}.
Context (preservesG : ∀ X Y : D,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).

(** The composite candidate still needs no target product choice. *)

(** 复合候选仍不需要目标积选择。 *)

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

(** 允许独立指定复合见证。 *)

Definition independent_product_inv_comp (X Y : C)
  : preserved_product_inv (G ∘F F) preservesGF X Y ≈
      fmap G (preserved_product_inv F preservesF X Y) ∘
        preserved_product_inv G preservesG (F X) (F Y)
  := preserved_product_inv_comp F G preservesF preservesG preservesGF X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.
Context {EE : HasExponential PE}.

(** Exponential composition requires neither terminal nor inverse data. *)

(** 指数复合不需要终对象或逆数据。 *)

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

(** ** 反向的范畴界

    分离所有原生对象、Hom、相等及辅助律层级，只在比较需要时引入选择。 *)

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

(** 候选保持性不选择目标积。 *)

Definition reversed_product_cone {X Y P : C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
  : is_product (F X) (F Y) (F P) (fmap F p) (fmap F q)
  := preserved_product_cone F preservesF HP.

Context {PD : HasProduct D}.
Context (preservesG : ∀ X Y : D,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).

(** The composite candidate still needs no target product choice. *)

(** 复合候选仍不需要目标积选择。 *)

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

(** 允许独立指定复合见证。 *)

Definition reversed_product_inv_comp (X Y : C)
  : preserved_product_inv (G ∘F F) preservesGF X Y ≈
      fmap G (preserved_product_inv F preservesF X Y) ∘
        preserved_product_inv G preservesG (F X) (F Y)
  := preserved_product_inv_comp F G preservesF preservesG preservesGF X Y.

Context {EC : HasExponential PC} {ED : HasExponential PD}.
Context {EE : HasExponential PE}.

(** Exponential composition requires neither terminal nor inverse data. *)

(** 指数复合不需要终对象或逆数据。 *)

Definition reversed_exp_comp (X Y : C)
  : exp_cmp (G ∘F F) preservesGF X Y ≈
      exp_cmp G preservesG (F X) (F Y) ∘
        fmap G (exp_cmp F preservesF X Y)
  := exp_cmp_comp F G
      preservesF preservesG preservesGF X Y.

End ReversedComposition.

(** Function exponentials require a separate choice. *)

(** 函数指数须另外选定。 *)

Fail Definition automatic_composition_exponentials
  : @HasExponential SetCat SetCat_HasProduct
  := ltac:(typeclasses eauto).

(** ** Two Reader Environments

    Use the standard setoid products and locally chosen exponentials. Reuse the
    general right-adjoint preservation theorem for exponentiation, rather
    than another pointwise product universal-property proof. *)

(** ** 两个 Reader 环境

    使用标准广集积和局部选定的指数；复用取指数的一般右伴随保持定理，不另证逐点积
    泛性质。 *)

Section ReaderComposition.
Local Instance composition_exponentials
  : HasExponential SetCat_HasProduct
  := SetCat_HasExponential.

(** Each stage reads one Boolean environment. *)

(** 每个阶段读取一个布尔环境。 *)

Definition CompositionReaderF
  : Fct SetCat SetCat
  := (-^ BoolS).

(** Product preservation is inherited from the product-exponential adjunction. *)

(** 积保持性继承自积与指数伴随。 *)

Definition composition_reader_products (X Y : SetC)
  : is_product (CompositionReaderF X) (CompositionReaderF Y)
      (CompositionReaderF ((X × Y)%ob))
      (fmap CompositionReaderF π1) (fmap CompositionReaderF π2)
  := exp_preserves_product BoolS product_universal.

(** Compose the supplied cones, without a CCC-functor input. *)

(** 复合给定锥，不输入 CCC 函子性质。 *)

Definition composition_readers_products (X Y : SetC)
  : is_product (CompositionReaderF (CompositionReaderF X))
      (CompositionReaderF (CompositionReaderF Y))
      (CompositionReaderF (CompositionReaderF ((X × Y)%ob)))
      (fmap CompositionReaderF (fmap CompositionReaderF π1))
      (fmap CompositionReaderF (fmap CompositionReaderF π2))
  := preserved_product_comp CompositionReaderF CompositionReaderF
      composition_reader_products composition_reader_products X Y.

(** The product equation uses the constructed composite witness. *)

(** 积方程使用构造出的复合见证。 *)

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

(** 指数分解使用相同的指定比较。 *)

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

(** 实际依赖环境的族返回带标签的值。 *)

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

(** 两个环境也给出非常值参数族。 *)

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

(** 直接比较保留两个环境的位置。 *)

Example composition_reader_direct_computes
  : exp_cmp
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS composition_reader_functions
      composition_reader_argument true false = (3%nat, false).
Proof. reflexivity. Defined.

(** Factoring the comparison computes the same result at those positions. *)

(** 比较的分解在这些位置计算出相同结果。 *)

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

(** 两种计算实际依赖给定的环境族。 *)

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

(** 改变参数会显露两个环境的作用。 *)

Example composition_reader_environment_computes
  : exp_cmp
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS composition_reader_functions
      composition_reader_constant_argument true false = (3%nat, true).
Proof. reflexivity. Defined.

(** Pairing through the composite retains its original universal mediator. *)

(** 经复合配对时保留原来的泛中介。 *)

Example composition_reader_product_computes
  : preserved_product_inv
      (CompositionReaderF ∘F CompositionReaderF) composition_readers_products
      TaggedGluingS TaggedGluingS
      (composition_reader_argument, composition_reader_constant_argument)
      true false = ((3%nat, true), (3%nat, false)).
Proof. reflexivity. Defined.

(** The factored inverse product map has the same native data computation. *)

(** 分解后的逆积映射具有相同的原生数据计算。 *)

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

(** 常恒等族具有不同的原生标签。 *)

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

(** 复合比较保持 Type 值函数相等，不识别函数或定律记录。 *)

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

(** 指定相等仍保留代表可观察的差异。 *)

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

(** ** 独立复合见证及不可逆比较

    在恒等之后使用常空函子，直接指定复合见证，而不使用
    [preserved_product_comp]。尽管此函子不可能保持终对象及指数，复合律
    依然适用。 *)

Section EmptyComposition.
Local Existing Instance SetCat_HasExponential.

(** Directly supplied preservation witnesses need not be equal records. *)

(** 直接指定的保持见证不必是相等记录。 *)

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

(** 指数比较的逆不进入复合定理。 *)

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

(** 逆将构造出空载体的元素。 *)

Definition composition_comparison_not_iso
  : is_iso (exp_cmp
      (ConstF SetCat EmptyS ∘F (@IdF SetCat))
      empty_constant_preserves_products BoolS BoolS) → Empty_set
  := empty_constant_comparison_not_iso.

(** Binary-product composition also supplies no terminal preservation. *)

(** 二元积复合也不给出终对象保持性。 *)

Definition composition_not_terminal
  : is_terminal ((ConstF SetCat EmptyS ∘F (@IdF SetCat)) UnitS) → Empty_set
  := empty_constant_not_terminal.

End EmptyComposition.
