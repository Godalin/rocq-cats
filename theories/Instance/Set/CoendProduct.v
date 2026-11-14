From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Diagram.Core
  Cat.Coend.Core
  Cat.End.Core
  Instance.Set.Core
  Instance.Set.Product.

(** * Products with a Chosen Coend *)

(** * 与选定 coend 取积 *)

(** Only the specified coend is assumed. Parameterized descent proves that
    products preserve it, without internal function objects or a comparison
    between carrier and equality universes. No chosen coend is registered
    globally by this module. *)

(** 只假定所指定的 coend。带参数下降证明积保持它，不使用内部函数对象，
    也不要求载体与相等宇宙之间的大小关系。本模块不全局注册选定 coend。 *)

(** ** Descent with a Setoid Parameter

    Fix a setoid-valued bifunctor with its selected coend. A respectful
    family of cowedges descends to a map on the product of that coend and
    the parameter setoid. Equality remains pointwise specified equality. *)

(** ** 带广集参数的下降

    固定广集值双函子及其选定 coend。保持相等的余楔族下降为该 coend 与
    参数广集之积上的映射；相等始终为逐点指定相等。 *)

Section ParameterDescent.
Universes u p.
Context {C : Cat} {F : Fct ((C^op) ×C C)
    (SetCat@{u p _ _ _ _ _})} `{HC : !HasCoend SetCat F}.

(** Descend separately at each parameter. Respectfulness in the parameter
    follows from uniqueness, rather than equality of mediator functions. *)

(** 分别在每个参数处下降；参数方向的保相等由唯一性导出，不使用中介函数相等。 *)

Program Definition coend_parameter_desc {W E : SetC@{u p}}
    (κ : W → Cowedge F E) (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
  : (coend[F] ×S W) →r E
  :=
  {|func zw := coend⟨κ (snd zw)⟩ (fst zw)
  |}.
Next Obligation.
  intros [z w] [z' w'] [Hz Hw]. cbn.
  transitivity (coend⟨κ w'⟩ z).
  - exact (@coend_desc_proper C SetCat F HC E
      (κ w) (κ w') (Hκ w w' Hw) z).
  - exact (@func_proper _ _ (coend⟨κ w'⟩) z z' Hz).
Defined.

(** Parameterized descent computes on every original injection. *)

(** 带参数下降在每个原注入上计算。 *)

Lemma coend_parameter_β {W E : SetC@{u p}}
    (κ : W → Cowedge F E) (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (X : @Ob C) (x : F (X, X)) (w : W)
  : coend_parameter_desc κ Hκ (ιcoend[F] X x, w) ≈S κ w X x.
Proof. exact (@coend_β C SetCat F HC E (κ w) X x). Defined.

(** Products of injections with parameters jointly distinguish maps. *)

(** 注入与参数的积联合地区分映射。 *)

Lemma coend_parameter_hom_ext {W E : SetC@{u p}}
    (f g : (coend[F] ×S W) →r E)
    (H : ∀ X (x : F (X, X)) (w : W),
      f (ιcoend[F] X x, w) ≈S g (ιcoend[F] X x, w))
  : f ≈f g.
Proof.
  intros [z w].
  unshelve epose (fw := ({|func a := f (a, w)|} : coend[F] →r E)).
  { intros a b Hab. apply func_proper. split; [exact Hab | reflexivity]. }
  unshelve epose (gw := ({|func a := g (a, w)|} : coend[F] →r E)).
  { intros a b Hab. apply func_proper. split; [exact Hab | reflexivity]. }
  exact (@coend_hom_ext C SetCat F HC E fw gw (λ X x, H X x w) z).
Defined.

(** The injection equations uniquely determine parameterized descent. *)

(** 注入方程唯一决定带参数下降。 *)

Lemma coend_parameter_unique {W E : SetC@{u p}}
    (κ : W → Cowedge F E) (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (f : (coend[F] ×S W) →r E)
    (H : ∀ X (x : F (X, X)) (w : W),
      f (ιcoend[F] X x, w) ≈S κ w X x)
  : f ≈f coend_parameter_desc κ Hκ.
Proof.
  apply coend_parameter_hom_ext. intros X x w.
  transitivity (κ w X x); [apply H | symmetry; apply coend_parameter_β].
Defined.

(** Pointwise equivalent families give equivalent mediators, independently
    of the chosen respectfulness witnesses. *)

(** 逐点等价的族给出等价中介，不依赖选用的保相等见证。 *)

Lemma coend_parameter_desc_proper {W E : SetC@{u p}}
    (κ μ : W → Cowedge F E)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (Hμ : Proper ([≈S] ==> CowedgeEq) μ)
    (H : ∀ w, κ w ≈CW μ w)
  : coend_parameter_desc κ Hκ ≈f coend_parameter_desc μ Hμ.
Proof.
  intros [z w]. exact (@coend_desc_proper C SetCat F HC E
    (κ w) (μ w) (H w) z).
Defined.

End ParameterDescent.

(** ** A Fixed Right Factor

    For a chosen coend of [F] and a fixed setoid [W], construct the cowedge
    into [coend[F] ×S W]. Slice any competing cowedge at [w : W] and reuse
    parameterized descent; no new quotient or existence axiom is needed. *)

(** ** 固定右因子

    给定 [F] 的选定 coend 及固定广集 [W]，构造指向 [coend[F] ×S W] 的余楔。
    将任意竞争余楔在 [w : W] 处切片后复用带参数下降，不另造商或存在公理。 *)

Section RightProduct.
Universes u p.
Context {C : Cat} (F : Fct ((C^op) ×C C)
    (SetCat@{u p _ _ _ _ _})) (W : SetC@{u p}).

(** Multiply each bifunctor value by the same right factor. *)

(** 每个双函子值与同一个右因子取积。 *)

Definition CoendProductRightF
  : Fct ((C^op) ×C C) SetCat
  := @PointwiseProductF _ SetCat SetCat_HasProduct F
      (@ConstF ((C^op) ×C C) SetCat W).

(** Holding the parameter fixed gives a cowedge of the original bifunctor. *)

(** 固定参数给出原双函子的余楔。 *)

Program Definition coend_product_slice {E : SetC@{u p}}
    (κ : Cowedge CoendProductRightF E) (w : W)
  : Cowedge F E
  := CowedgeOf (D := SetCat) (F := F) (W := E)
      (λ X, {|func x := κ X (x, w)|}) _.
Next Obligation.
  intros x y H. apply func_proper. split; [exact H | reflexivity].
Defined.
Next Obligation.
  intros x. exact (@cowedge_comm C SetCat CoendProductRightF E κ
    X Y f (x, w)).
Defined.

(** Slices form a respectful parameter family. *)

(** 切片组成保持参数相等的族。 *)

Global Instance coend_product_slice_proper {E : SetC@{u p}}
    (κ : Cowedge CoendProductRightF E)
  : Proper ([≈S] ==> CowedgeEq) (coend_product_slice κ).
Proof.
  intros w w' H X x.
  exact (@func_proper _ _ (κ X) (x, w) (x, w')
    (reflexivity x, H)).
Defined.

Context `{HC : !HasCoend SetCat F}.

(** Pair the original coend injections with the unchanged parameter. *)

(** 将原 coend 注入与不变参数配对。 *)

Program Definition coend_product_right_cowedge
  : Cowedge CoendProductRightF (coend[F] ×S W)
  := CowedgeOf (D := SetCat) (F := CoendProductRightF)
      (W := coend[F] ×S W)
      (λ X, {|func xw := (ιcoend[F] X (fst xw), snd xw)|}) _.
Next Obligation.
  intros [x w] [x' w'] [H K]. split; [apply func_proper |]; assumption.
Defined.
Next Obligation.
  intros [x w]. split; [| reflexivity].
  exact (@cowedge_comm C SetCat F (coend[F]) ιcoend[F] X Y f x).
Defined.

(** Descend from the product by the same parameterized mediator. *)

(** 用同一个带参数中介从积下降。 *)

Definition coend_product_right_desc {E : SetC@{u p}}
    (κ : Cowedge CoendProductRightF E)
  : (coend[F] ×S W) →r E
  := coend_parameter_desc (coend_product_slice κ)
      (coend_product_slice_proper κ).

(** Product descent computes at each paired injection. *)

(** 积下降在每个配对注入处计算。 *)

Lemma coend_product_right_β {E : SetC@{u p}}
    (κ : Cowedge CoendProductRightF E) (X : @Ob C)
  : (coend_product_right_desc κ ∘r coend_product_right_cowedge X) ≈f κ X.
Proof.
  intros [x w].
  exact (@coend_parameter_β C F HC W E (coend_product_slice κ)
    (coend_product_slice_proper κ) X x w).
Defined.

(** The product cowedge is universal. Its witness retains the transparent
    parameterized mediator and its pointwise uniqueness. *)

(** 积余楔是泛余楔，其见证保留透明的带参数中介及其逐点唯一性。 *)

Definition coend_product_right_universal
  : is_coend coend_product_right_cowedge.
Proof.
  apply (snd (coend_universal_iff coend_product_right_cowedge)).
  intros E κ. exists (coend_product_right_desc κ). split.
  - intros X. exact (coend_product_right_β κ X).
  - intros f H.
    apply (@coend_parameter_unique C F HC W E (coend_product_slice κ)
      (coend_product_slice_proper κ) f). intros X x w.
    exact (H X (x, w)).
Defined.

(** Explicitly select this product coend; importing the module alone does
    not replace other choices. *)

(** 显式选择此积 coend；单独导入模块不会替换其他选择。 *)

Program Definition SetCat_CoendProductRight
  : HasCoend SetCat CoendProductRightF
  :=
  {|hasOpEnd :=
      {|EndObj := coend[F] ×S W
      ; end_wedge := op_wedge coend_product_right_cowedge
      ; end_universal := coend_product_right_universal
      |}
  |}.

End RightProduct.

(** ** A Fixed Left Factor

    Keep the same hypotheses and interchange product coordinates. The
    mediator and its uniqueness still come from parameterized descent;
    this is not a second quotient construction. *)

(** ** 固定左因子

    保持相同假设并交换积坐标；中介及其唯一性仍来自带参数下降，
    并非第二套商构造。 *)

Section LeftProduct.
Universes u p.
Context {C : Cat} (F : Fct ((C^op) ×C C)
    (SetCat@{u p _ _ _ _ _})) (W : SetC@{u p}).

(** Multiply each bifunctor value by the same left factor. *)

(** 每个双函子值与同一个左因子取积。 *)

Definition CoendProductLeftF
  : Fct ((C^op) ×C C) SetCat
  := @PointwiseProductF _ SetCat SetCat_HasProduct
      (@ConstF ((C^op) ×C C) SetCat W) F.

(** Coordinate exchange identifies the two product kernels naturally. *)

(** 坐标交换自然地联系两个积核。 *)

Program Definition CoendProductSwapN
  : CoendProductRightF F W ⇒ CoendProductLeftF
  :=
  {|nt X := {|func xw := (snd xw, fst xw)|}
  |}.
Next Obligation. intros [x w] [x' w'] [H K]. split; assumption. Defined.
Next Obligation. intros [x w]. split; reflexivity. Defined.

Context `{HC : !HasCoend SetCat F}.

(** Pair the unchanged left parameter with the original injections. *)

(** 将不变的左参数与原注入配对。 *)

Program Definition coend_product_left_cowedge
  : Cowedge CoendProductLeftF (W ×S coend[F])
  := CowedgeOf (D := SetCat) (F := CoendProductLeftF)
      (W := W ×S coend[F])
      (λ X, {|func wx := (fst wx, ιcoend[F] X (snd wx))|}) _.
Next Obligation.
  intros [w x] [w' x'] [H K]. split; [exact H | apply func_proper; exact K].
Defined.
Next Obligation.
  intros [w x]. split; [reflexivity |].
  exact (@cowedge_comm C SetCat F (coend[F]) ιcoend[F] X Y f x).
Defined.

(** Exchange the parameter coordinate and reuse right-product descent. *)

(** 交换参数坐标并复用右积下降。 *)

Program Definition coend_product_left_desc {E : SetC@{u p}}
    (κ : Cowedge CoendProductLeftF E)
  : (W ×S coend[F]) →r E
  :=
  {|func wz := coend_product_right_desc F W
      (cowedge_precompose κ CoendProductSwapN) (snd wz, fst wz)
  |}.
Next Obligation.
  intros [w z] [w' z'] [H K].
  exact (@func_proper _ _ (coend_product_right_desc F W
    (cowedge_precompose κ CoendProductSwapN)) (z, w) (z', w') (K, H)).
Defined.

(** The same descent computation gives the left injection equation. *)

(** 同一个下降计算给出左注入方程。 *)

Lemma coend_product_left_β {E : SetC@{u p}}
    (κ : Cowedge CoendProductLeftF E) (X : @Ob C)
  : (coend_product_left_desc κ ∘r coend_product_left_cowedge X) ≈f κ X.
Proof.
  intros [w x].
  exact (@coend_product_right_β C F W HC E
    (cowedge_precompose κ CoendProductSwapN) X (x, w)).
Defined.

(** Universality follows from the original parameterized distinction law. *)

(** 泛性质来自原来的带参数区分定律。 *)

Definition coend_product_left_universal
  : is_coend coend_product_left_cowedge.
Proof.
  apply (snd (coend_universal_iff coend_product_left_cowedge)).
  intros E κ. exists (coend_product_left_desc κ). split.
  - intros X. exact (coend_product_left_β κ X).
  - intros f H [w z].
    unshelve epose (fw := ({|func zw := f (snd zw, fst zw)|}
      : (coend[F] ×S W) →r E)).
    { intros [a b] [a' b'] [Ha Hb]. apply func_proper. split; assumption. }
    exact (@coend_parameter_unique C F HC W E
      (coend_product_slice F W (cowedge_precompose κ CoendProductSwapN))
      (coend_product_slice_proper F W
        (cowedge_precompose κ CoendProductSwapN)) fw
      (λ X x w, H X (w, x)) (z, w)).
Defined.

(** Enable the left product choice explicitly, with the same mediator. *)

(** 显式启用左积选择，保留同一个中介。 *)

Program Definition SetCat_CoendProductLeft
  : HasCoend SetCat CoendProductLeftF
  :=
  {|hasOpEnd :=
      {|EndObj := W ×S coend[F]
      ; end_wedge := op_wedge coend_product_left_cowedge
      ; end_universal := coend_product_left_universal
      |}
  |}.

End LeftProduct.

(** ** Comparison with Other Chosen Product Coends

    If a product kernel already has a selected coend, its universal
    property compares it to the product constructed above. No identification
    of choices, representatives or law witnesses is required. *)

(** ** 与其他选定积 coend 比较

    若积核已有选定 coend，由泛性质将其与上述积构造比较；
    不认同选择、代表或定律见证。 *)

Section ProductComparisons.
Universes u p.
Context {C : Cat} (F : Fct ((C^op) ×C C)
    (SetCat@{u p _ _ _ _ _})) (W : SetC@{u p})
    `{HC : !HasCoend SetCat F}.

(** Any chosen right-product coend is canonically isomorphic to the product. *)

(** 任意选定右积 coend 与积典范同构。 *)

Definition CoendProductRightIso
    `{HR : !HasCoend SetCat (CoendProductRightF F W)}
  : coend[CoendProductRightF F W] ≅[SetCat] (coend[F] ×S W)
  := coend_unique (coend_universal (CoendProductRightF F W))
      (coend_product_right_universal F W).

(** The comparison sends each generator to its original injection and parameter. *)

(** 比较将每个生成元送到原注入及参数。 *)

Lemma coend_product_right_iso_β
    `{HR : !HasCoend SetCat (CoendProductRightF F W)} (X : @Ob C)
  : (CoendProductRightIso.1 ∘r ιcoend[CoendProductRightF F W] X)
    ≈f coend_product_right_cowedge F W X.
Proof.
  exact (coend_unique_β (coend_universal (CoendProductRightF F W))
    (coend_product_right_universal F W) X).
Defined.

(** The left comparison uses the same universal uniqueness theorem. *)

(** 左比较使用同一个泛唯一性定理。 *)

Definition CoendProductLeftIso
    `{HL : !HasCoend SetCat (CoendProductLeftF F W)}
  : coend[CoendProductLeftF F W] ≅[SetCat] (W ×S coend[F])
  := coend_unique (coend_universal (CoendProductLeftF F W))
      (coend_product_left_universal F W).

(** Its generator equation keeps the left parameter unchanged. *)

(** 其生成元方程保持左参数不变。 *)

Lemma coend_product_left_iso_β
    `{HL : !HasCoend SetCat (CoendProductLeftF F W)} (X : @Ob C)
  : (CoendProductLeftIso.1 ∘r ιcoend[CoendProductLeftF F W] X)
    ≈f coend_product_left_cowedge F W X.
Proof.
  exact (coend_unique_β (coend_universal (CoendProductLeftF F W))
    (coend_product_left_universal F W) X).
Defined.

(** The inverse comparison reinserts every right-product representative. *)

(** 逆比较重新插入每个右积代表。 *)

Lemma coend_product_right_iso_inv_β
    `{HR : !HasCoend SetCat (CoendProductRightF F W)} (X : @Ob C)
  : (CoendProductRightIso.2.1 ∘r coend_product_right_cowedge F W X)
    ≈f ιcoend[CoendProductRightF F W] X.
Proof.
  intros xw.
  transitivity (CoendProductRightIso.2.1
    (CoendProductRightIso.1 (ιcoend[CoendProductRightF F W] X xw))).
  - exact (@func_proper _ _ CoendProductRightIso.2.1
      (coend_product_right_cowedge F W X xw)
      (CoendProductRightIso.1 (ιcoend[CoendProductRightF F W] X xw))
      (symmetry (coend_product_right_iso_β X xw))).
  - exact (fst CoendProductRightIso.2.2
      (ιcoend[CoendProductRightF F W] X xw)).
Defined.

(** Coordinate exchange gives the corresponding left reinsertion equation. *)

(** 坐标交换给出对应的左重新插入方程。 *)

Lemma coend_product_left_iso_inv_β
    `{HL : !HasCoend SetCat (CoendProductLeftF F W)} (X : @Ob C)
  : (CoendProductLeftIso.2.1 ∘r coend_product_left_cowedge F W X)
    ≈f ιcoend[CoendProductLeftF F W] X.
Proof.
  intros wx.
  transitivity (CoendProductLeftIso.2.1
    (CoendProductLeftIso.1 (ιcoend[CoendProductLeftF F W] X wx))).
  - exact (@func_proper _ _ CoendProductLeftIso.2.1
      (coend_product_left_cowedge F W X wx)
      (CoendProductLeftIso.1 (ιcoend[CoendProductLeftF F W] X wx))
      (symmetry (coend_product_left_iso_β X wx))).
  - exact (fst CoendProductLeftIso.2.2
      (ιcoend[CoendProductLeftF F W] X wx)).
Defined.

End ProductComparisons.
