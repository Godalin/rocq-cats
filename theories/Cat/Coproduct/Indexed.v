From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Limit.Core
  Cat.Limit.Reindex
  Cat.Limit.Transport.
From Cats Require Export
  Cat.Colimit.Core
  Cat.Diagram.DualShape.

(** * Indexed Coproducts as Discrete Colimits *)

(** * 指标余积作为离散余极限 *)

Notation "'∐[' D ']'" := (Colim (DiscreteF D)) : ob_scope.

(** The injection is the selected discrete colimit's leg. *)

(** 注入就是选定离散余极限的锥腿。 *)

Definition indexed_inj {C : Cat} {I : Type} {D : I → @Ob C}
    `{HC : !HasColimit C (DiscreteF D)} (i : I)
  : Hom (D i) ∐[D]
  := ιcolim[DiscreteF D] i.

Notation "'ι∐[' D ']'" := (indexed_inj (D := D)) : hom_scope.

(** Copair a family of arrows with common codomain by the original opposite
    limit mediator. *)

(** 用原反范畴极限中介，对具有共同余域的箭头族作余配对。 *)

Definition indexed_copair {C : Cat} {I : Type} {D : I → @Ob C}
    `{HC : !HasColimit C (DiscreteF D)}
    {X : @Ob C} (κ : ∀ i, Hom (D i) X)
  : Hom ∐[D] X
  := @colimit_desc (DiscreteCat I) C (DiscreteF D) HC X
      (@DiscreteCocone C I (DiscreteF D) X κ).

Notation "'∐⟨' κ '⟩'" := (indexed_copair κ) : hom_scope.

(** ** Laws of an Indexed Coproduct

    Fix an object family [D] indexed by [I] and a chosen colimit of its
    discrete diagram. Derive the injection and copairing laws using the
    specified hom equality. *)

(** ** 指标余积的定律

    固定以 [I] 为指标的对象族 [D] 及其离散图式的选定余极限，用指定 Hom 相等导出内射及余配对定律。 *)

Section IndexedCoproduct.
Context {C : Cat} {I : Type} {D : I → @Ob C}
    `{HC : !HasColimit C (DiscreteF D)}.

(** Restricting an indexed copair to an injection recovers its component. *)

(** 将指标余配对限制到注入，恢复其分量。 *)

Lemma indexed_coproduct_β {X : @Ob C} (κ : ∀ i, Hom (D i) X) (i : I)
  : ∐⟨κ⟩ ∘ ι∐[D] i ≈ κ i.
Proof. exact (colimit_β (DiscreteCocone (D := DiscreteF D) κ) i). Qed.

(** All injection composites recover an arrow out of the coproduct. *)

(** 全部注入复合恢复从余积出发的箭头。 *)

Lemma indexed_coproduct_η {X : @Ob C} (f : Hom ∐[D] X)
  : ∐⟨λ i, f ∘ ι∐[D] i⟩ ≈ f.
Proof.
  transitivity (colim⟨f ∘Cocone ιcolim[DiscreteF D]⟩).
  - apply colimit_desc_proper. intros i. reflexivity.
  - apply colimit_η.
Qed.

(** Copairing respects the pointwise specified arrow equality. *)

(** 余配对保持逐点指定箭头相等。 *)

Global Instance indexed_copair_proper {X : @Ob C}
  : Proper ((λ κ μ : ∀ i, Hom (D i) X, ∀ i, κ i ≈ μ i) ==>
      @HomEq C ∐[D] X) indexed_copair.
Proof. intros κ μ H. apply colimit_desc_proper. exact H. Qed.

(** Postcomposition of indexed copairs acts componentwise. *)

(** 指标余配对的后合成逐分量作用。 *)

Lemma indexed_coproduct_comp {X Y : @Ob C}
    (f : Hom X Y) (κ : ∀ i, Hom (D i) X)
  : f ∘ ∐⟨κ⟩ ≈ ∐⟨λ i, f ∘ κ i⟩.
Proof.
  unfold indexed_copair.
  rewrite <- (colimit_desc_comp f (DiscreteCocone (D := DiscreteF D) κ)).
  apply colimit_desc_proper. intros i. reflexivity.
Qed.

(** All injections together detect equality of coproduct-valued domains. *)

(** 全部注入共同检测以余积为定义域的箭头相等。 *)

Theorem indexed_coproduct_hom_ext {X : @Ob C} (f g : Hom ∐[D] X)
    (H : ∀ i, f ∘ ι∐[D] i ≈ g ∘ ι∐[D] i)
  : f ≈ g.
Proof.
  rewrite <- (indexed_coproduct_η f), <- (indexed_coproduct_η g).
  apply indexed_copair_proper. exact H.
Qed.

End IndexedCoproduct.

(** Read one indexed coproduct as its opposite indexed product, keeping its
    selected apex. Discrete reindexing and identity-component transport only
    adapt diagrams; they do not require a choice for other object families. *)

(** 将单个指标余积读作其反指标积并保留选定顶点；离散重索引及恒等分量运输仅适配
    图式，不要求为其他对象族作出选择。 *)

Definition IndexedCoproductOpProduct {C : Cat} {I : Type}
    (D : I → @Ob C) `{HC : !HasColimit C (DiscreteF D)}
  : HasLimit (C^op) (@DiscreteF (C^op) I D)
  := @TransportedLimit (DiscreteCat I) (C^op)
      ((DiscreteF D)^opF ∘F OpDiscreteF I) (@DiscreteF (C^op) I D)
      ((discrete_functor_nat_iso ((DiscreteF D)^opF ∘F OpDiscreteF I)).1
        ^-1N (discrete_functor_nat_iso
          ((DiscreteF D)^opF ∘F OpDiscreteF I)).2)
      (NatIso_inv_NatIso _ (discrete_functor_nat_iso
        ((DiscreteF D)^opF ∘F OpDiscreteF I)).2)
      (@RestrictedLimit (DiscreteCat I) ((DiscreteCat I)^op) (C^op)
        (OpDiscreteF I) (op_discrete_full I)
        (op_discrete_essentially_surjective I) ((DiscreteF D)^opF)
        (@hasOpLimit C _ _ HC)).

(** Adapt one opposite discrete limit to the ordinary discrete colimit.
    Only the shape changes by its full, essentially surjective reversal. *)

(** 将单个反离散极限适配为通常离散余极限，仅沿满且本质满的反转改变形状。 *)

Program Definition DiscreteDiagramColimit {C : Cat} {I : Type}
    (D : Functor (DiscreteCat I) C)
    `{HL : !HasLimit (C^op) (D^opF ∘F OpDiscreteF I)}
  : HasColimit C D
  :=
  {|hasOpLimit := ReindexedLimit (op_discrete_full I)
      (op_discrete_essentially_surjective I) (D^opF)
  |}.

(** Opposite discrete limits choose ordinary indexed coproducts. *)

(** 反离散极限选择通常指标余积。 *)

Program Definition OpDiscreteColimits {C : Cat} {I : Type}
    `{HL : !HasLimitsOfShape (C^op) (DiscreteCat I)}
  : HasColimitsOfShape C (DiscreteCat I)
  :=
  {|hasOpLimits := ReindexedLimits (op_discrete_full I)
      (op_discrete_essentially_surjective I)
  |}.

(** Read ordinary discrete colimits as opposite discrete limits using the
    inverse shape comparison. Selected structures remain explicitly enabled. *)

(** 用逆形状比较将通常离散余极限读作反离散极限；选定结构仍须显式启用。 *)

Definition DiscreteColimitsOpLimits {C : Cat} {I : Type}
    `{HC : !HasColimitsOfShape C (DiscreteCat I)}
  : HasLimitsOfShape (C^op) (DiscreteCat I)
  := @ReindexedLimits ((DiscreteCat I)^op) (DiscreteCat I) (C^op)
      (UnopDiscreteF I) (unop_discrete_full I)
      (unop_discrete_essentially_surjective I) (@hasOpLimits C _ HC).
