From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Arrow.Core
  Cat.Equalizer.
From Cats Require Export Cat.Product.Indexed.

(** * Constructing Limits from Products and Equalizers

    Only two particular products are needed: one over the objects and one over
    the arrows of the index category. Their size bounds remain explicit in the
    chosen product assumptions. *)

(** * 由积和等化子构造极限

    只需要两个特定的积，分别由形状的对象与箭头索引；大小约束保留在选定积的假设
    中。 *)

Definition DiagramObjects {J C : Cat} (D : Functor J C) (j : @Ob J)
  : @Ob C
  := D j.
(** Index target objects by all arrows of the diagram shape. *)

(** 用图式形状的全部箭头索引其目标对象。 *)

Definition DiagramTargets {J C : Cat} (D : Functor J C) (a : ArrowOb J)
  : @Ob C
  := D (arrow_cod a).

(** The shared universal-property argument only needs that cone families
    equalize the constraints and that the proposed legs factor through the
    object product. Different presentations may supply these constraints. *)

(** 共享的泛性质证明仅需锥分量等化约束，且候选锥腿经过对象积。不同表示可以提供
    不同的约束映射。 *)

Definition product_cone_equalizer_limit {J C : Cat} (D : Functor J C)
    `{HO : !HasLimit C (DiscreteF (DiagramObjects D))}
    {Q E : @Ob C} {s t : Hom Π[DiagramObjects D] Q}
    {e : Hom E Π[DiagramObjects D]}
    (κ : E ⇒Δ D) (Hκ : ∀ j, κ j ≈ πΠ[DiagramObjects D] j ∘ e)
    (Hcones : ∀ X (μ : X ⇒Δ D),
      s ∘ indexed_pair (D := DiagramObjects D) (λ j, μ j) ≈
      t ∘ indexed_pair (D := DiagramObjects D) (λ j, μ j))
    (HE : is_equalizer s t E e)
  : is_limit κ.
Proof.
  intros X μ.
  pose (p := indexed_pair (D := DiagramObjects D) (λ j, μ j)).
  destruct (snd HE X p (Hcones X μ)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros j.
    change (κ j ∘ h ≈ μ j).
    rewrite (Hκ j), comp_assoc, (@this _ _ _ _ _ Hh).
    unfold p. apply (indexed_product_β (D := DiagramObjects D)).
  - intros k Hk. apply (@that _ _ _ _ _ Hh).
    apply indexed_product_hom_ext. intros j.
    rewrite <- comp_assoc, <- (Hκ j). transitivity (μ j).
    + exact (Hk j).
    + unfold p. symmetry. apply (indexed_product_β (D := DiagramObjects D)).
Defined.

Section ProductsEqualizer.
Context {J C : Cat} (D : Functor J C).
Context `{HO : !HasLimit C (DiscreteF (DiagramObjects D))}.
Context `{HA : !HasLimit C (DiscreteF (DiagramTargets D))}.

(** The constraint map whose components apply each diagram arrow after its
    source projection. *)

(** 约束映射的分量先取源投影，再应用图式箭头。 *)

Definition diagram_product_source
  : Hom Π[DiagramObjects D] Π[DiagramTargets D]
  := Π⟨λ a, fmap D (arrow_map a) ∘ πΠ[DiagramObjects D] (arrow_dom a)⟩.

(** The constraint map whose components are target projections. *)

(** 以目标投影为各分量的约束映射。 *)

Definition diagram_product_target
  : Hom Π[DiagramObjects D] Π[DiagramTargets D]
  := Π⟨λ a, πΠ[DiagramObjects D] (arrow_cod a)⟩.

(** Equalizing the two product constraints makes the proposed legs commute. *)

(** 等化两个积约束后，候选锥腿交换。 *)

Lemma diagram_product_comm {E : @Ob C} (e : Hom E Π[DiagramObjects D])
    (H : diagram_product_source ∘ e ≈ diagram_product_target ∘ e)
    {i j : @Ob J} (f : Hom i j)
  : fmap D f ∘ (πΠ[DiagramObjects D] i ∘ e) ≈ πΠ[DiagramObjects D] j ∘ e.
Proof.
  pose (a := ({|arrow_dom := i
              ; arrow_cod := j
              ; arrow_map := f
              |} : ArrowOb J)).
  transitivity ((πΠ[DiagramTargets D] a ∘ diagram_product_source) ∘ e).
  - unfold diagram_product_source. rewrite indexed_product_β, comp_assoc. reflexivity.
  - rewrite comp_assoc, H, <- comp_assoc.
    unfold diagram_product_target. rewrite indexed_product_β. reflexivity.
Qed.

(** The cone obtained by composing an equalizer inclusion with object
    projections. *)

(** 将等化子包含箭头与对象积投影复合得到的锥。 *)

Program Definition ProductsEqualizerCone {E : @Ob C}
    (e : Hom E Π[DiagramObjects D])
    (H : diagram_product_source ∘ e ≈ diagram_product_target ∘ e)
  : E ⇒Δ D
  :=
  {|nt j := πΠ[DiagramObjects D] j ∘ e
  |}.
Next Obligation.
  rewrite comp_id_r. symmetry. apply diagram_product_comm. exact H.
Qed.

(** The equalizer of the two product constraints has the limiting property. *)

(** 两个积约束的等化子具有极限性质。 *)

Definition products_equalizer_limit {E : @Ob C} {e : Hom E Π[DiagramObjects D]}
    (H : diagram_product_source ∘ e ≈ diagram_product_target ∘ e)
    (HE : is_equalizer diagram_product_source diagram_product_target E e)
  : is_limit (ProductsEqualizerCone e H).
Proof.
  refine (product_cone_equalizer_limit D (ProductsEqualizerCone e H) _ _ HE).
  - intros j. reflexivity.
  - intros X μ. apply indexed_product_hom_ext. intros a.
    unfold diagram_product_source, diagram_product_target.
    rewrite <- !comp_assoc, !indexed_product_β, comp_assoc, !indexed_product_β.
    pose proof (nt_naturality μ (arrow_map a)) as Hμ.
    cbn in Hμ. rewrite comp_id_r in Hμ.
    transitivity (μ (arrow_cod a)).
    + symmetry. exact Hμ.
    + symmetry. apply (indexed_product_β (D := DiagramObjects D)).
Defined.

(** Select a diagram limit using its two indexed products and an equalizer. *)

(** 利用两个索引积及等化子选择图式极限。 *)

Program Definition ProductsEqualizerLimit `{HE : !HasEqualizer C}
  : HasLimit C D
  :=
  {|Lim := Eq[diagram_product_source, diagram_product_target]
  ; limit_cone := ProductsEqualizerCone
      ιeq[diagram_product_source, diagram_product_target] equalizer_comm
  |}.
Next Obligation. apply products_equalizer_limit. exact equalizer_universal. Defined.

End ProductsEqualizer.

(** Uniform product choices give all limits of the shape. No new choice of
    maps or functoriality laws is needed for the resulting limit functor. *)

(** 统一选择所需积后即可构造该形状的全部选定极限；其极限函子不需要重新选择映射
    或函子律。 *)

Program Definition IndexedProductsEqualizerLimits {J C : Cat}
    `{HO : !HasLimitsOfShape C (DiscreteCat (@Ob J))}
    `{HA : !HasLimitsOfShape C (DiscreteCat (ArrowOb J))}
    `{HE : !HasEqualizer C}
  : HasLimitsOfShape C J
  :=
  {|hasLimit D := ProductsEqualizerLimit D
  |}.
