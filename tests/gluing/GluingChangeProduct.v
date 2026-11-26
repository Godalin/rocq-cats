From Cats Require Import
  Cat.Gluing.ChangeProduct
  Cat.Diagram.Core
  Cat.Morphism
  Cat.Functor.Cartesian
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Bool.Group.
From CatsTests.gluing Require Import
  Gluing.

(** * Gluing Model Change Preserving Binary Products

    Strict category profiles test the weak preservation interface without
    terminal assumptions. A constant-unit interpretation admits a
    noninvertible compatibility boundary. A separate constant-Boolean
    base change fails to preserve a product, despite compatibility. *)

(** ** Independent Category Levels

    Keep the four categories' object, hom, equality and auxiliary law
    bounds separate. Supply image universal properties without choices
    in the target categories. *)

Section IndependentGluingProducts.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2 o3 h3 e3 l3.
Constraint h0 < e0, e0 < o0, o0 < l0.
Constraint e1 < h1, h1 < o1, o1 < l1.
Constraint h2 < e2, e2 < o2, o2 < l2.
Constraint e3 < h3, h3 < o3, o3 < l3.
Constraint l0 < o1, l1 < o2, l2 < o3.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context {X Y P : Gluing F} (p : Hom P X) (q : Hom P Y).

(** The candidate needs only the three supplied image products. *)

Definition independent_gluing_product_cone
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
  := gluing_change_product_cone H K α p q left right image.

Context {PC : HasProduct C} {PD : HasProduct D}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ A B : D,
    is_product (K A) (K B) (K ((A × B)%ob)) (fmap K π1) (fmap K π2)).
Context (image : ∀ A B : C,
    is_product (F' (H A)) (F' (H B)) (F' (H ((A × B)%ob)))
      (fmap F' (fmap H π1)) (fmap F' (fmap H π2))).

(** The chosen source cone retains these strict boundaries. *)

Definition independent_gluing_product (U V : Gluing F)
  : @is_product (Gluing F')
      (GluingChangeF H K α U) (GluingChangeF H K α V)
      (GluingChangeF H K α (@Prod _ (Gluing_HasProduct F source) U V))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π1 _ (Gluing_HasProduct F source) U V))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π2 _ (Gluing_HasProduct F source) U V))
  := gluing_change_product H K α source base target image U V.

End IndependentGluingProducts.

(** ** Reversed Category Levels

    Keep the four categories' object, hom, equality and auxiliary law
    bounds separate. Supply image universal properties without choices
    in the target categories. *)

Section ReversedGluingProducts.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2 o3 h3 e3 l3.
Constraint e0 < h0, h0 < o0, o0 < l0.
Constraint h1 < e1, e1 < o1, o1 < l1.
Constraint e2 < h2, h2 < o2, o2 < l2.
Constraint h3 < e3, e3 < o3, o3 < l3.
Constraint l3 < o2, l2 < o1, l1 < o0.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context {X Y P : Gluing F} (p : Hom P X) (q : Hom P Y).

(** The candidate needs only the three supplied image products. *)

Definition reversed_gluing_product_cone
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
  := gluing_change_product_cone H K α p q left right image.

Context {PC : HasProduct C} {PD : HasProduct D}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ A B : D,
    is_product (K A) (K B) (K ((A × B)%ob)) (fmap K π1) (fmap K π2)).
Context (image : ∀ A B : C,
    is_product (F' (H A)) (F' (H B)) (F' (H ((A × B)%ob)))
      (fmap F' (fmap H π1)) (fmap F' (fmap H π2))).

(** The chosen source cone retains these strict boundaries. *)

Definition reversed_gluing_product (U V : Gluing F)
  : @is_product (Gluing F')
      (GluingChangeF H K α U) (GluingChangeF H K α V)
      (GluingChangeF H K α (@Prod _ (Gluing_HasProduct F source) U V))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π1 _ (Gluing_HasProduct F source) U V))
      (fmap (GluingChangeF H K α)
        (@Cats.Cat.Product.Core.π2 _ (Gluing_HasProduct F source) U V))
  := gluing_change_product H K α source base target image U V.

End ReversedGluingProducts.

(** The standard setoid product is a designated default; extracting the
    choice still gives its original transparent mediator. *)

Definition default_change_set_products
  : HasProduct SetCat
  := ltac:(typeclasses eauto).

Example default_change_set_product_choice
  : default_change_set_products = SetCat_HasProduct.
Proof. reflexivity. Qed.

(** Importing preservation does not select products in a gluing model. *)

Fail Definition automatic_changed_gluing_products
  : HasProduct (Gluing (ConstF SetCat UnitS))
  := ltac:(typeclasses eauto).

(** ** A Compatible Noninvertible Collapse

    Use the standard setoid products. Both model-change functors are
    identity, and the new interpretation is constant unit. Compatibility
    collapses each setoid to unit; binary-product preservation survives
    although the component at the tagged setoid is not invertible. *)

Section UnitCollapse.

(** The constant-unit interpretation preserves each binary cone. *)

Definition unit_model_product (A B : SetCat)
  : is_product UnitS UnitS UnitS id id.
Proof.
  intros Z f g. exists f. split.
  - split; intros z; exact tt.
  - intros k _ z. exact tt.
Defined.

(** The compatibility components use the original terminal mediators. *)

Program Definition ProductUnitBoundaryN
  : (@CompF SetCat SetCat SetCat (@IdF SetCat) (@IdF SetCat)) ⇒
      (@CompF SetCat SetCat SetCat (ConstF SetCat UnitS) (@IdF SetCat))
  :=
  {|nt X := @term SetCat SetCat_HasTerminal X
  ; nat_naturality X Y f x := tt
  |}.

(** An inverse would send the same unit value to both zero and one. *)

Definition product_boundary_not_iso
  : is_iso (ProductUnitBoundaryN TaggedGluingS) → Empty_set.
Proof.
  intro H.
  destruct (fst H.2 (0%nat, false)) as [zero token0].
  destruct (fst H.2 (1%nat, false)) as [one token1].
  cbn in zero, one. rewrite zero in one. discriminate one.
Defined.

(** Explicitly select the existing source gluing products. *)

Local Instance binary_source_products
  : HasProduct (Gluing (@IdF SetCat))
  := Gluing_HasProduct IdF (λ A B, product_universal).

(** Explicitly select the target gluing products independently. *)

Local Instance binary_target_products
  : HasProduct (Gluing (ConstF SetCat UnitS))
  := Gluing_HasProduct (ConstF SetCat UnitS) unit_model_product.

(** Model change keeps both side maps while collapsing the interpretation. *)

Definition UnitProductChangeF
  : Fct (Gluing (@IdF SetCat)) (Gluing (ConstF SetCat UnitS))
  := GluingChangeF (@IdF SetCat) (@IdF SetCat) ProductUnitBoundaryN.

(** The actual mapped selected cone is a product under the weak theorem. *)

Definition unit_changed_product (X Y : Gluing (@IdF SetCat))
  : @is_product (Gluing (ConstF SetCat UnitS))
      (UnitProductChangeF X) (UnitProductChangeF Y)
      (UnitProductChangeF ((X × Y)%ob))
      (fmap UnitProductChangeF π1) (fmap UnitProductChangeF π2)
  := gluing_change_product IdF IdF ProductUnitBoundaryN
      (λ A B, product_universal) (λ A B, product_universal)
      (λ A B, product_universal) unit_model_product X Y.

(** The optional stronger input explicitly names its source choices. *)

Program Definition unit_interpretation_cartesian
  : IsCartF (ConstF SetCat UnitS) SetCat_HasTerminal SetCat_HasProduct
  :=
  {|fct_terminal := @terminal_universal SetCat SetCat_HasTerminal
  ; fct_product := unit_model_product
  |}.

(** The stronger wrapper supplies only the missing image-product input. *)

Definition unit_changed_product_strong (X Y : Gluing (@IdF SetCat))
  : @is_product (Gluing (ConstF SetCat UnitS))
      (UnitProductChangeF X) (UnitProductChangeF Y)
      (UnitProductChangeF ((X × Y)%ob))
      (fmap UnitProductChangeF π1) (fmap UnitProductChangeF π2)
  := gluing_change_product_from_cartesian IdF IdF ProductUnitBoundaryN
      (HF' := unit_interpretation_cartesian)
      (λ A B, product_universal) (λ A B, product_universal)
      (λ A B, product_universal) X Y.

(** The comparison uses the explicit source and target choices above. *)

Definition UnitProductComparison
  : UnitProductChangeF ((TaggedGluingObj × TaggedGluingObj)%ob) ≅
      (UnitProductChangeF TaggedGluingObj ×
        UnitProductChangeF TaggedGluingObj)%ob
  := gluing_change_product_iso IdF IdF ProductUnitBoundaryN
      (λ A B, product_universal) (λ A B, product_universal)
      (λ A B, product_universal) unit_model_product _ _.

(** The separately named inverse retains the general image mediator. *)

Definition unit_product_comparison_inv
  : Hom (UnitProductChangeF TaggedGluingObj ×
        UnitProductChangeF TaggedGluingObj)%ob
      (UnitProductChangeF ((TaggedGluingObj × TaggedGluingObj)%ob))
  := gluing_change_product_inv IdF IdF ProductUnitBoundaryN
      (λ A B, product_universal) (λ A B, product_universal)
      (λ A B, product_universal) unit_model_product _ _.

(** Both inverse equations refer to the same selected source cone. *)

Definition unit_product_comparison_β
  : (fmap UnitProductChangeF π1 ∘ unit_product_comparison_inv ≈ π1) ∧
    (fmap UnitProductChangeF π2 ∘ unit_product_comparison_inv ≈ π2)
  := gluing_change_product_inv_β IdF IdF ProductUnitBoundaryN
      (λ A B, product_universal) (λ A B, product_universal)
      (λ A B, product_universal) unit_model_product _ _.

(** The general pairing equation applies to a tag-changing input. *)

Definition unit_changed_pair_law
  : fmap UnitProductChangeF ⟨tagged_gluing_toggle, id⟩ ≈
      unit_product_comparison_inv ∘
        ⟨fmap UnitProductChangeF tagged_gluing_toggle,
          fmap UnitProductChangeF id⟩
  := gluing_change_pair IdF IdF ProductUnitBoundaryN
      (λ A B, product_universal) (λ A B, product_universal)
      (λ A B, product_universal) unit_model_product tagged_gluing_toggle id.

(** The mapped structural arrow computes to the intended unit value. *)

Example unit_changed_structure_computes
  : comma_arrow (UnitProductChangeF TaggedGluingObj) (3, false) = tt.
Proof. reflexivity. Defined.

(** The comparison's left map preserves both input tags. *)

Example unit_product_comparison_left_computes
  : comma_left UnitProductComparison.1 ((3, false), (4, true)) =
      ((3, false), (4, true)).
Proof. reflexivity. Defined.

(** Its base map preserves the independent base input. *)

Example unit_product_comparison_right_computes
  : comma_right UnitProductComparison.1 ((5, true), (6, false)) =
      ((5, true), (6, false)).
Proof. reflexivity. Defined.

(** The saved inverse left map also computes natively. *)

Example unit_product_inverse_left_computes
  : comma_left UnitProductComparison.2.1 ((3, false), (4, true)) =
      ((3, false), (4, true)).
Proof. reflexivity. Defined.

(** The separately named inverse retains its right computational map. *)

Example unit_product_inverse_right_computes
  : comma_right unit_product_comparison_inv ((5, true), (6, false)) =
      ((5, true), (6, false)).
Proof. reflexivity. Defined.

(** The actual image universal property pairs the mapped square inputs. *)

Example unit_image_mediator_computes
  : comma_left (unit_changed_product TaggedGluingObj TaggedGluingObj _
      (fmap UnitProductChangeF tagged_gluing_toggle)
      (fmap UnitProductChangeF id)).1 (3, false) =
      ((3, true), (3, false)).
Proof. reflexivity. Defined.

(** The stronger wrapper retains the independent right mediator's value. *)

Example unit_strong_image_mediator_computes
  : comma_right (unit_changed_product_strong TaggedGluingObj
      TaggedGluingObj _ (fmap UnitProductChangeF tagged_gluing_toggle)
      (fmap UnitProductChangeF id)).1 (4, true) =
      ((4, false), (4, true)).
Proof. reflexivity. Defined.

(** The image cone's projection equation retains a Boolean equality token. *)

Example unit_image_projection_token_computes
  : snd (fst (fst (this
      (unit_changed_product TaggedGluingObj TaggedGluingObj _
        (fmap UnitProductChangeF tagged_gluing_toggle)
        (fmap UnitProductChangeF id)).2)) (3, false)) = false.
Proof. reflexivity. Defined.

(** Mapped pairing respects tag-changing designated equality. *)

Example unit_changed_pair_respects
  : fmap UnitProductChangeF ⟨tagged_gluing_toggle, tagged_gluing_toggle⟩ ≈
      fmap UnitProductChangeF ⟨id, id⟩.
Proof.
  rewrite tagged_gluing_toggle_equal. reflexivity.
Qed.

End UnitCollapse.

(** ** Failure without Endpoint Product Preservation

    Keep the same two interpretations and identity target-category change,
    but change every base object to Boolean. The compatibility boundary
    still exists and the constant-unit interpretation preserves all image
    cones. Both base legs become identity, and a cone with different
    Boolean legs cannot factor. No chosen target products are needed. *)

Section NonproductBase.
Local Instance counter_source_products
  : HasProduct (Gluing (@IdF SetCat))
  := Gluing_HasProduct IdF (λ A B, product_universal).

(** This natural boundary exists even though the base change loses products. *)

Program Definition NonproductBaseBoundaryN
  : (@CompF SetCat SetCat SetCat (@IdF SetCat) (@IdF SetCat)) ⇒
      (@CompF SetCat SetCat SetCat (ConstF SetCat UnitS)
        (ConstF SetCat BoolS))
  :=
  {|nt X := @term SetCat SetCat_HasTerminal X
  ; nat_naturality X Y f x := tt
  |}.

(** The actual compatible Gluing change is still a functor. *)

Definition NonproductBaseChangeF
  : Fct (Gluing (@IdF SetCat)) (Gluing (ConstF SetCat UnitS))
  := GluingChangeF (ConstF SetCat BoolS) (@IdF SetCat)
      NonproductBaseBoundaryN.

(** A unit-based target gluing object tests both Boolean legs. *)

Program Definition NonproductConeOb
  : Gluing (ConstF SetCat UnitS)
  :=
  {|comma_left_ob := UnitS
  ; comma_right_ob := UnitS
  ; comma_arrow := id
  |}.

(** Choose each base Boolean independently; compatibility sees only unit. *)

Program Definition nonproduct_cone_leg (b : bool)
  : Hom NonproductConeOb (NonproductBaseChangeF TaggedGluingObj)
  :=
  {|comma_left := tagged_gluing_point 0%nat
  ; comma_right := {|func x := b
                   ; func_proper x y h := eq_refl
                   |}
  ; comma_comm x := tt
  |}.

(** The two required base projection equations force true to equal false. *)

Definition compatible_change_not_product
  : @is_product (Gluing (ConstF SetCat UnitS))
      (NonproductBaseChangeF TaggedGluingObj)
      (NonproductBaseChangeF TaggedGluingObj)
      (NonproductBaseChangeF ((TaggedGluingObj × TaggedGluingObj)%ob))
      (fmap NonproductBaseChangeF π1) (fmap NonproductBaseChangeF π2) →
      Empty_set.
Proof.
  intro HP.
  destruct (HP NonproductConeOb (nonproduct_cone_leg true)
    (nonproduct_cone_leg false)) as [h [[H1 H2] Hu]].
  pose proof (snd H1 tt) as one. pose proof (snd H2 tt) as other.
  cbn in one, other. rewrite one in other. discriminate other.
Defined.

(** The failed cone's first base leg is still an actual identity map. *)

Example nonproduct_base_leg_computes
  : comma_right (fmap NonproductBaseChangeF
      (@Cats.Cat.Product.Core.π1 _ counter_source_products
        TaggedGluingObj TaggedGluingObj)) true = true.
Proof. reflexivity. Defined.

End NonproductBase.
