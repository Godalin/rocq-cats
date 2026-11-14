From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Arrow.Core
  Cat.Equalizer
  Cat.Product.Equalizer.
From Cats Require Export
  Cat.End.Core.

(** * Ends from Products and an Equalizer *)

(** * 由积和等化子构造 end *)

(** The first product collects diagonal values. The second collects one
    off-diagonal value for each arrow. Its index stores endpoints and the
    arrow, without an equality witness from the index category. *)

(** 第一个积收集对角值，第二个积为每条箭头收集一个非对角值。后者的指标保留端点
    和箭头，不存储指标范畴的相等见证。 *)

Definition EndDiag {C D : Cat} (F : Fct ((C^op) ×C C) D)
    (X : @Ob C)
  : @Ob D
  := F (X, X).

(** For an arrow [X → Y], the constraint codomain is [F (X,Y)]. *)

(** 对于箭头 [X → Y]，约束的值域为 [F (X,Y)]。 *)

Definition EndTargets {C D : Cat} (F : Fct ((C^op) ×C C) D)
    (a : ArrowOb C)
  : @Ob D
  := F (arrow_dom a, arrow_cod a).

(** ** Two Product Constraints

    Fix a mixed-variance bifunctor and just the two indicated products.
    A wedge is exactly a diagonal family equalizing these two constraints;
    a candidate equalizer therefore supplies an end. *)

(** ** 两条积约束

    固定混合变元双函子及上述两个特定积。楔正是等化这两条约束的对角族，因此候选
    等化子给出 end。 *)

Section ProductsEqualizer.
Context {C D : Cat} (F : Fct ((C^op) ×C C) D).
Context `{HO : !HasLimit D (DiscreteF (EndDiag F))}.
Context `{HA : !HasLimit D (DiscreteF (EndTargets F))}.

(** Apply the covariant arrow action after the source diagonal projection. *)

(** 在源的对角投影后应用协变箭头作用。 *)

Definition end_product_covariant
  : Hom ∏[EndDiag F] ∏[EndTargets F]
  := indexed_pair (D := EndTargets F) (λ a, fmap F
      (X := (arrow_dom a, arrow_dom a))
      (Y := (arrow_dom a, arrow_cod a)) (id, arrow_map a)
      ∘ π∏[EndDiag F] (arrow_dom a)).

(** Apply the contravariant arrow action after the target diagonal projection. *)

(** 在目标的对角投影后应用逆变箭头作用。 *)

Definition end_product_contravariant
  : Hom ∏[EndDiag F] ∏[EndTargets F]
  := indexed_pair (D := EndTargets F) (λ a, fmap F
      (X := (arrow_cod a, arrow_cod a))
      (Y := (arrow_dom a, arrow_cod a)) (arrow_map a, id)
      ∘ π∏[EndDiag F] (arrow_cod a)).

(** Equalizing the constraints makes the projected family a wedge. *)

(** 等化约束使投影族成为楔。 *)

Lemma end_product_comm {E : @Ob D} (e : Hom E ∏[EndDiag F])
    (H : end_product_covariant ∘ e ≈ end_product_contravariant ∘ e)
    {X Y : @Ob C} (f : Hom X Y)
  : fmap F (X := (X, X)) (Y := (X, Y)) (id, f)
      ∘ (π∏[EndDiag F] X ∘ e)
    ≈ fmap F (X := (Y, Y)) (Y := (X, Y)) (f, id)
      ∘ (π∏[EndDiag F] Y ∘ e).
Proof.
  pose (a := ({|arrow_dom := X
              ; arrow_cod := Y
              ; arrow_map := f
              |} : ArrowOb C)).
  transitivity ((π∏[EndTargets F] a ∘ end_product_covariant) ∘ e).
  - unfold end_product_covariant.
    rewrite indexed_product_β, comp_assoc. reflexivity.
  - rewrite comp_assoc, H, <- comp_assoc.
    unfold end_product_contravariant.
    rewrite indexed_product_β, comp_assoc. reflexivity.
Qed.

(** The equalizer inclusion followed by the diagonal projections is a wedge. *)

(** 等化子包含后接对角投影组成楔。 *)

Program Definition ProductsEqualizerWedge {E : @Ob D}
    (e : Hom E ∏[EndDiag F])
    (H : end_product_covariant ∘ e ≈ end_product_contravariant ∘ e)
  : Wedge F E
  :=
  {|wedge_leg X := π∏[EndDiag F] X ∘ e
  |}.
Next Obligation. apply end_product_comm. exact H. Qed.

(** Every wedge equalizes the two constraints after diagonal pairing. *)

(** 每个楔在对角配对后等化两条约束。 *)

Lemma end_product_equalizes {W} (κ : Wedge F W)
  : end_product_covariant ∘ indexed_pair (D := EndDiag F) (λ X, κ X)
    ≈ end_product_contravariant ∘ indexed_pair (D := EndDiag F) (λ X, κ X).
Proof.
  apply indexed_product_hom_ext. intros a.
  unfold end_product_covariant, end_product_contravariant.
  rewrite <- !comp_assoc, !indexed_product_β, !comp_assoc.
  rewrite (@indexed_product_β D _ (EndDiag F) HO W _ (arrow_dom a)).
  rewrite (@indexed_product_β D _ (EndDiag F) HO W _ (arrow_cod a)).
  apply wedge_comm.
Qed.

(** The full end property reuses unique factorization of constrained families. *)

(** 完整 end 性质复用受约束族的唯一分解。 *)

Definition products_equalizer_end {E : @Ob D}
    {e : Hom E ∏[EndDiag F]}
    (H : end_product_covariant ∘ e ≈ end_product_contravariant ∘ e)
    (HE : is_equalizer end_product_covariant end_product_contravariant E e)
  : is_end (ProductsEqualizerWedge e H).
Proof.
  intros W κ.
  exact (indexed_product_equalizer_universal (EndDiag F)
    HE W (λ X, κ X) (end_product_equalizes κ)).
Defined.

(** A single candidate equalizer suffices to select the end. *)

(** 单个候选等化子就足以选取 end。 *)

Program Definition ProductsEqualizerEndOf {E : @Ob D}
    (e : Hom E ∏[EndDiag F])
    (HE : is_equalizer end_product_covariant end_product_contravariant E e)
  : HasEnd D F
  :=
  {|EndObj := E
  ; end_wedge := ProductsEqualizerWedge e (fst HE)
  ; end_universal := products_equalizer_end (fst HE) HE
  |}.

(** Selected equalizers supply that particular candidate automatically.
    No completeness structure for other diagrams is required. *)

(** 从两个特定积和选定等化子选取一个 end，不要求其他图式的完备结构。 *)

Program Definition ProductsEqualizerEnd `{HE : !HasEqualizer D}
  : HasEnd D F
  := ProductsEqualizerEndOf
      ιeq[end_product_covariant, end_product_contravariant] equalizer_universal.

End ProductsEqualizer.
