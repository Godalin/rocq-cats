From Cats Require Export
  Cat.Gluing.Change
  Cat.Gluing.Cartesian.
From Cats Require Import
  Cat.Comma.ChangeProduct
  Cat.Functor.Cartesian
  Cat.Functor.ProductPreservation.

(** * Binary Products under Gluing Model Change

    For [α : K F ⇒ F' H], recognize image products through the accepted
    comma-cone theorem. The two endpoint image cones and their right
    [F']-image must have the product universal property. The boundary [α]
    need not be invertible. No terminal object, exponential or selected
    target product is needed for the weak preservation theorem.

    With explicitly supplied target products, the original generic
    comparisons give an isomorphism and its transparent inverse. This
    does not assert terminal or exponential preservation. *)

(** * 粘合模型变化下的二元积

    对 [α : K F ⇒ F' H]，通过已接收的逗号锥定理识别像积。两端像锥及
    其右侧 [F'] 像须具有积泛性质；边界 [α] 无须可逆。弱保持定理不需要
    终对象、指数或选定目标积。

    显式给出目标积后，原有一般比较提供同构及其透明逆；本模块不声称终对象
    或指数保持。 *)

(** ** A Supplied Image Cone

    Fix a model change and an arbitrary source cone. Supply just the
    three image universal properties, independently of source choices
    or source universality. The original comma square action is reused. *)

(** ** 给定像锥

    固定模型变化和任意源锥，只给出三个像泛性质，与来源选择或来源泛性质
    无关；复用原有逗号方形作用。 *)

Section GluingChangeProductCone.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context {X Y P : Gluing F} (p : Hom P X) (q : Hom P Y).

(** Endpoint image products and the relevant interpretation image product
    suffice. No inverse of a boundary component is used. *)

(** 两端像积与相关解释像积已经足够；不使用任何边界分量的逆。 *)

Definition gluing_change_product_cone
    (left : is_product (K (comma_left_ob X)) (K (comma_left_ob Y))
      (K (comma_left_ob P)) (fmap K (comma_left p))
      (fmap K (comma_left q)))
    (right : is_product (H (comma_right_ob X)) (H (comma_right_ob Y))
      (H (comma_right_ob P)) (fmap H (comma_right p))
      (fmap H (comma_right q)))
    (image : is_product (F' (H (comma_right_ob X)))
      (F' (H (comma_right_ob Y))) (F' (H (comma_right_ob P)))
      (fmap F' (fmap H (comma_right p)))
      (fmap F' (fmap H (comma_right q))))
  : @is_product (Gluing F')
      (GluingChangeF H K α X) (GluingChangeF H K α Y)
      (GluingChangeF H K α P)
      (fmap (GluingChangeF H K α) p) (fmap (GluingChangeF H K α) q)
  := comma_change_product_cone K H K (GluingChangeLeftBoundaryN K) α
      p q left right image.

End GluingChangeProductCone.

(** ** Preservation of the Selected Source Products

    Choose binary products in [C] and [D] and assume [F] preserves the
    selected base cones, as required by the existing gluing construction.
    Require [H] and [K] to preserve those endpoint cones, and [F'] to
    preserve the resulting [H]-image base cones. No target choices or
    terminal preservation enter this theorem. *)

(** ** 选定来源积的保持

    在 [C]、[D] 中选择二元积，按原粘合构造的要求假设 [F] 保持选定基锥。
    要求 [H]、[K] 保持这些端点锥，并要求 [F'] 保持得到的 [H] 像基锥。
    本定理不涉及目标选择或终对象保持。 *)

Section GluingChangeProducts.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ A B : D,
    is_product (K A) (K B) (K ((A × B)%ob)) (fmap K π1) (fmap K π2)).
Context (image : ∀ A B : C,
    is_product (F' (H A)) (F' (H B)) (F' (H ((A × B)%ob)))
      (fmap F' (fmap H π1)) (fmap F' (fmap H π2))).

(** The existing source gluing choice fixes the cone sent by model change.
    Recognize its actual image without replacing its structure arrow. *)

(** 既有来源粘合选择确定由模型变化映射的锥；识别其实际像，不替换结构箭头。 *)

Definition gluing_change_product (X Y : Gluing F)
  : @is_product (Gluing F')
      (GluingChangeF H K α X) (GluingChangeF H K α Y)
      (GluingChangeF H K α (@Prod _ (Gluing_HasProduct F source) X Y))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π1 _ (Gluing_HasProduct F source) X Y))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π2 _ (Gluing_HasProduct F source) X Y))
  := gluing_change_product_cone H K α
      (@Cats.Cat.Product.Core.π1 _ (Gluing_HasProduct F source) X Y)
      (@Cats.Cat.Product.Core.π2 _ (Gluing_HasProduct F source) X Y)
      (target (comma_left_ob X) (comma_left_ob Y))
      (base (comma_right_ob X) (comma_right_ob Y))
      (image (comma_right_ob X) (comma_right_ob Y)).

(** ** Comparisons with an Explicit Target Choice

    Supply any chosen products of the target gluing category explicitly.
    Reuse the general preservation comparisons and pairing law with the
    same source choice; no choice is registered by importing this module. *)

(** ** 与显式目标选择的比较

    显式给出目标粘合范畴的任意选定积，在同一来源选择上复用一般保持比较及
    配对定律。导入本模块不会注册任何选择。 *)

Section GluingChangeProductComparisons.
Context `{PG : !HasProduct (Gluing F')}.

(** Compare the image product with the selected target product by an
    isomorphism rather than native equality of objects or law records. *)

(** 用同构比较像积与选定目标积，不要求对象或定律记录原生相等。 *)

Definition gluing_change_product_iso (X Y : Gluing F)
  : GluingChangeF H K α (@Prod _ (Gluing_HasProduct F source) X Y) ≅
      (GluingChangeF H K α X × GluingChangeF H K α Y)%ob
  := preserved_product_iso (GluingChangeF H K α) gluing_change_product X Y.

(** The inverse uses exactly the supplied endpoint image mediators. *)

(** 逆恰使用给定的端点像中介。 *)

Definition gluing_change_product_inv (X Y : Gluing F)
  : Hom (GluingChangeF H K α X × GluingChangeF H K α Y)%ob
      (GluingChangeF H K α (@Prod _ (Gluing_HasProduct F source) X Y))
  := preserved_product_inv (GluingChangeF H K α) gluing_change_product X Y.

(** Both inverse projection equations reuse the generic comparison law. *)

(** 逆的两个投影方程复用一般比较定律。 *)

Definition gluing_change_product_inv_β (X Y : Gluing F)
  : (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π1 _ (Gluing_HasProduct F source) X Y) ∘
      gluing_change_product_inv X Y ≈ π1) ∧
    (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π2 _ (Gluing_HasProduct F source) X Y) ∘
      gluing_change_product_inv X Y ≈ π2)
  := preserved_product_inv_β (GluingChangeF H K α) gluing_change_product X Y.

(** Mapped pairing factors through the retained inverse comparison. *)

(** 配对的像通过保留的逆比较分解。 *)

Definition gluing_change_pair {X Y Z : Gluing F}
    (f : Hom Z X) (g : Hom Z Y)
  : fmap (GluingChangeF H K α)
      (@pair _ (Gluing_HasProduct F source) X Y Z f g) ≈
      gluing_change_product_inv X Y ∘
        ⟨fmap (GluingChangeF H K α) f, fmap (GluingChangeF H K α) g⟩
  := preserved_pair (GluingChangeF H K α) gluing_change_product f g.

End GluingChangeProductComparisons.
End GluingChangeProducts.

(** ** A Sufficient Cartesian Interpretation

    Keep the weak source and endpoint binary-product hypotheses. If [F']
    is supplied as a cartesian functor for named source choices in [C'],
    its existing candidate-product preservation theorem supplies the last
    image cone. This optional stronger input is not needed above, and
    still asserts only binary-product preservation by the gluing change. *)

(** ** 足够的笛卡尔解释

    保留弱的来源及端点二元积假设。若对 [C'] 中具名来源选择给出 [F'] 的
    笛卡尔函子性质，则其既有候选积保持定理提供最后一个像锥。以上接口不
    要求此较强可选输入；此处仍只断言粘合变化保持二元积。 *)

Section CartesianInterpretation.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context `{TC' : !HasTerminal C'} `{PC' : !HasProduct C'}.
Context `{HF' : !IsCartF F' TC' PC'}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ A B : D,
    is_product (K A) (K B) (K ((A × B)%ob)) (fmap K π1) (fmap K π2)).

(** Interpret the base image product using only the previously proved
    cartesian-functor theorem, without another universal-property proof. *)

(** 只使用已证明的笛卡尔函子定理解释基像积，不另证泛性质。 *)

Definition gluing_change_product_from_cartesian (X Y : Gluing F)
  : @is_product (Gluing F')
      (GluingChangeF H K α X) (GluingChangeF H K α Y)
      (GluingChangeF H K α (@Prod _ (Gluing_HasProduct F source) X Y))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π1 _ (Gluing_HasProduct F source) X Y))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π2 _ (Gluing_HasProduct F source) X Y))
  := gluing_change_product H K α source base target
      (λ A B, cartesian_preserves_product F' (base A B)) X Y.

End CartesianInterpretation.
