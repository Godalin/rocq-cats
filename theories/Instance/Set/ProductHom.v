From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Product.Transport
  Instance.Set.Core
  Instance.Set.Product.

(** * Product Hom-Setoid Correspondence *)

(** * 积的 Hom 广集对应 *)

Section ProductHom.
Context {C : Cat} `{HP : !HasProduct C}.

(** Take the two projections of a product-valued arrow. *)

(** 取积值箭头的两个投影。 *)

Program Definition product_hom_split_resp {X Y Z : @Ob C}
  : HomSet Z (X × Y) →r (HomSet Z X ×S HomSet Z Y)
  :=
  {|func f := (π1 ∘ f, π2 ∘ f)
  |}.
Next Obligation. intros f g H. split; rewrite H; reflexivity. Defined.

(** Pair two hom-setoid elements. *)

(** 配对两个 Hom 广集元素。 *)

Program Definition product_hom_pair_resp {X Y Z : @Ob C}
  : (HomSet Z X ×S HomSet Z Y) →r HomSet Z (X × Y)
  :=
  {|func fg := ⟨fst fg, snd fg⟩
  |}.
Next Obligation.
  intros [f g] [f' g'] [H K]. apply product_pair_proper; assumption.
Defined.

(** The product universal property is an isomorphism of native hom-setoids,
    with no ambient selected setoid product structure. *)

(** 积泛性质为原生 Hom 广集同构，不要求环境中的选定广集积结构。 *)

Definition product_hom_iso (X Y Z : @Ob C)
  : HomSet Z (X × Y) ≅[SetCat] (HomSet Z X ×S HomSet Z Y).
Proof.
  exists product_hom_split_resp, product_hom_pair_resp. split.
  - intros f. symmetry. apply product_η.
  - intros [f g]. split; [apply product_β1 | apply product_β2].
Defined.

(** Changing context commutes with both components of the correspondence. *)

(** 上下文变换与对应的两个分量交换。 *)

Lemma product_hom_natural {W X Y Z : @Ob C}
    (h : Hom Z (X × Y)) (σ : Hom W Z)
  : product_hom_split_resp (h ∘ σ) ≈S
      (π1 ∘ h ∘ σ, π2 ∘ h ∘ σ).
Proof. split; symmetry; apply comp_assoc. Qed.

End ProductHom.
