From Cats Require Export
  Cat.Monoidal.Bifunctor.
From Cats Require Import
  Cat.Bicategory.Core.

Local Open Scope bicat_scope.

(** * Endomorphism Monoidal Categories

    Horizontal composition supplies the tensor of [B(X,X)]. All coherence
    is inherited from the bicategory, without a new strictness assumption.
    This construction does not require products or a terminal object in
    the hom-category. *)

(** * 自同态幺半范畴

    水平复合给出 [B(X,X)] 的张量，全部相干性继承自双范畴，不增加严格性假设，
    也不要求 Hom 范畴具有积或终对象。 *)

Section Endomorphisms.
Context (B : Bicat) (X : ObB B).

(** The bicategory associator, organized as a natural transformation on
    triples of endomorphisms. *)

(** 将双范畴结合子组织为自同态三元组上的自然变换。 *)

Program Definition EndoAssociatorN
  : TensorLeftF (@comp1F B X X X) ⇒ TensorRightF (@comp1F B X X X)
  :=
  {|nt '((h, g), f) := @associator B X X X X h g f
  |}.
Next Obligation.
  destruct X0 as [[h g] f0], Y as [[h' g'] f1], f as [[γ β] α]. cbn.
  exact (@associator_naturality B X X X X _ _ _ _ _ _
    γ β α).
Defined.

(** The bicategory left unitor is natural on the endohom category. *)

(** 双范畴左单位子在自同态范畴上自然。 *)

Program Definition EndoLeftUnitorN
  : π2F (@comp1F B X X X) (id1 (Bicat := B) X) ⇒ IdF
  :=
  {|nt f := @left_unitor B X X f
  |}.
Next Obligation. exact (@left_unitor_naturality B X X _ _ f). Defined.

(** The bicategory right unitor is natural on the endohom category. *)

(** 双范畴右单位子在自同态范畴上自然。 *)

Program Definition EndoRightUnitorN
  : π1F (@comp1F B X X X) (id1 (Bicat := B) X) ⇒ IdF
  :=
  {|nt f := @right_unitor B X X f
  |}.
Next Obligation. exact (@right_unitor_naturality B X X _ _ f). Defined.

(** The endomorphism monoidal structure is an explicit choice. Tensor order
    is the composition order: the left factor follows the right factor.
    Inverse components, naturality, pentagon and triangle are inherited. *)

(** 自同态幺半结构是显式选取。张量采用复合次序：左因子在右因子之后作用。
    逆分量、自然性、五边形与三角形均从已有结构继承。 *)

Program Definition EndoMonoidal
  : MonoidalCat (@HomCat B X X)
  := BifunctorMonoidal (@comp1F B X X X) (𝟙₁ X)
    (EndoAssociatorN;
      λ '((h, g), f), @associator_iso B X X X X h g f)
    (EndoLeftUnitorN;
      λ f, @left_unitor_iso B X X f)
    (EndoRightUnitorN;
      λ f, @right_unitor_iso B X X f)
    _ _.
Next Obligation. exact (bicat_pentagon W X0 Y Z). Defined.
Next Obligation. exact (bicat_triangle X0 Y). Defined.

(** The derived tensor of two cells agrees with horizontal composition. *)

(** 两个胞腔的导出张量与水平复合相等。 *)

Lemma endomorphism_tensor_map {f f' g g' : Cell1 X X}
    (β : Cell2 g g') (α : Cell2 f f')
  : @tensor_map (@HomCat B X X) EndoMonoidal g g' f f' β α ≈
      comp2_h β α.
Proof. apply bifunctor_monoidal_map. Qed.

End Endomorphisms.
