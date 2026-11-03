From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Adjunction
  Cat.Diagram.Dual
  Cat.Colimit.Core.

(** * Colimits as Left Adjoints to the Diagonal *)

(** * 余极限作为对角函子的左伴随 *)

Section ChosenColimits.
Context {J C : Cat} `{HC : !HasColimitsOfShape C J}.

(** Postcompose the selected injections as a respectful hom-setoid map. *)

(** 将选定注入后合成，得到保相等的 Hom 广集映射。 *)

Program Definition colimit_cocone_resp {D : Functor J C} {X : @Ob C}
  : HomSet (colim D) X →r @HomSet (Fct J C) D (ConstF J X)
  :=
  {|func f := f ∘Cocone ιcolim[D]
  |}.
Next Obligation. intros f g H j. cbn. rewrite H. reflexivity. Defined.

(** Extract the universal descending arrow as a respectful hom map. *)

(** 将提取泛下降箭头组织为保相等 Hom 映射。 *)

Program Definition colimit_desc_resp {D : Functor J C} {X : @Ob C}
  : @HomSet (Fct J C) D (ConstF J X) →r HomSet (colim D) X
  :=
  {|func := colimit_desc
  |}.

(** The selected-colimit functor is left adjoint to the diagonal. Its hom
    naturality follows from the universal mediator laws. *)

(** 选定余极限函子左伴随于对角函子；Hom 自然性来自泛中介定律。 *)

Definition ColimitAdjunction
  : ColimitF ⊣ Δ[J,C].
Proof.
  refine (AdjunctionFromHom ColimitF Δ[J,C]
    (λ D X, colimit_cocone_resp) (λ D X, colimit_desc_resp) _ _ _ _).
  - intros D X f. apply colimit_η.
  - intros D X κ. apply colimit_β.
  - intros D E X f α j.
    change ((f ∘ colimit_map α) ∘ ιcolim[E] j ≈
      (f ∘ ιcolim[D] j) ∘ α j).
    rewrite comp_assoc, (colimit_map_β α j). symmetry. apply comp_assoc.
  - intros D X Y k f j. cbn. apply comp_assoc.
Defined.

End ChosenColimits.

Section DiagonalAdjunction.
Context {J C : Cat} {L : Functor (Fct J C) C} (A : L ⊣ Δ[J,C]).

(** The unit of a diagonal adjunction supplies a chosen colimit cocone. *)

(** 对角伴随的单位给出选定余极限余锥。 *)

Program Definition DiagonalAdjunctionColimit (D : Functor J C)
  : HasColimit C D
  :=
  {|Colim := L D
  ; colimit_cocone := adjunction_unit A D
  |}.
Next Obligation.
  apply (snd (colimit_universal_iff (adjunction_unit A D))).
  intros X κ. exists (κ^♭[A]). refine {|this := _
                                      ; that := _
                                      |}.
  - intros j.
    exact (transitivity (symmetry (adjunct_unit A (κ^♭[A]) j))
      (adjunction_η A κ j)).
  - intros f H. apply (fst (adjunct_iff A f κ)).
    rewrite adjunct_unit. exact H.
Defined.

(** A left adjoint to the diagonal supplies all colimits of this shape.
    Selected structures are enabled only by explicit use of this constructor. *)

(** 对角函子的左伴随给出该形状的全部余极限；选定结构仅通过显式构造启用。 *)

Program Definition DiagonalAdjunctionColimits
  : HasColimitsOfShape C J
  :=
  {|hasColimit := DiagonalAdjunctionColimit
  |}.

End DiagonalAdjunction.

(** Chosen colimits of a shape and a chosen left adjoint to its diagonal
    construct each other, without equality of chosen structure records. *)

(** 某形状的选定余极限与其对角函子的选定左伴随相互构造，不比较选定结构记录。 *)

Theorem colimits_iff_diagonal_left_adjoint (J C : Cat)
  : HasColimitsOfShape C J ↔ ∃ L : Functor (Fct J C) C, L ⊣ Δ[J,C].
Proof.
  split.
  - intros HC. exists (@ColimitF J C HC). exact (@ColimitAdjunction J C HC).
  - intros [L A]. exact (DiagonalAdjunctionColimits A).
Defined.
