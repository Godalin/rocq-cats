From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Adjunction
  Cat.Diagram.Dual
  Cat.Limit.Core
  Cat.Limit.Adjunction
  Cat.Limit.Transport
  Cat.Colimit.Core.

(** * Colimit Adjunctions through Opposite Limit Adjunctions *)

(** * 通过反范畴极限伴随提供余极限伴随 *)

Section ChosenColimits.
Context {J C : Cat} `{HC : !HasColimitsOfShape C J}.
Let A
  := @LimitAdjunction (J^op) (C^op) _.

(** The forward hom map is the original limit adjunction's inverse map,
    read through the ordinary natural-transformation interface. *)

(** 正向 Hom 映射就是原极限伴随的逆映射，经通常自然变换接口读出。 *)

Program Definition colimit_cocone_resp {D : Functor J C} {X : @Ob C}
  : HomSet (colim D) X →r @HomSet (Fct J C) D (ConstF J X)
  :=
  {|func f := CoconeN {|op_cone := unadjunct A f|}
  |}.
Next Obligation.
  intros f g H j. exact (unadjunct_proper A f g H j).
Defined.

(** The inverse hom map is the original forward limit-adjunction map. *)

(** 逆向 Hom 映射就是原极限伴随的正向映射。 *)

Program Definition colimit_desc_resp {D : Functor J C} {X : @Ob C}
  : @HomSet (Fct J C) D (ConstF J X) →r HomSet (colim D) X
  :=
  {|func κ := adjunct A (op_cone (CoconeOfN κ))
  |}.
Next Obligation.
  intros κ μ H.
  exact (adjunct_proper A (op_cone (CoconeOfN κ))
    (op_cone (CoconeOfN μ)) (λ j, H j)).
Defined.

(** Assemble the ordinary adjunction interface from the existing opposite
    limit adjunction. All inverse and naturality laws are inherited. *)

(** 从已有反范畴极限伴随组装通常的伴随接口；互逆律与自然性全部继承。 *)

Definition ColimitAdjunction
  : ColimitF ⊣ Δ[J,C].
Proof.
  refine (AdjunctionFromHom ColimitF Δ[J,C]
    (λ D X, colimit_cocone_resp) (λ D X, colimit_desc_resp) _ _ _ _).
  - intros D X f.
    transitivity (adjunct A (unadjunct A f)).
    + apply (adjunct_proper A). intros j. reflexivity.
    + exact (adjunction_η A f).
  - intros D X κ j. exact (adjunction_β A (op_cone (CoconeOfN κ)) j).
  - intros D E X f α j. exact (unadjunct_comp_l A (α^opN) f j).
  - intros D X Y k f j. exact (unadjunct_comp_r A f k j).
Defined.

End ChosenColimits.

Section DiagonalAdjunction.
Context {J C : Cat} {L : Functor (Fct J C) C} (A : L ⊣ Δ[J,C]).

(** The existing unit universal property supplies the opposite limit
    directly; no separate colimit uniqueness proof is needed. *)

(** 已有单位泛性质直接给出反范畴极限，无须另证余极限中介唯一性。 *)

Program Definition DiagonalAdjunctionColimit (D : Functor J C)
  : HasColimit C D
  :=
  {|hasOpLimit :=
      {|Lim := L D
      ; limit_cone := op_cone (CoconeOfN (adjunction_unit A D))
      |}
  |}.
Next Obligation.
  intros X μ.
  exists ((CoconeN {|op_cone := μ|})^♭[A]).
  exact (adjunction_unit_universal A (CoconeN {|op_cone := μ|})).
Defined.

(** Read any opposite-shape diagram in the original categories, use the
    same unit construction, then transport its limit back along [OpUnopF]. *)

(** 将任意反形状图式读回原范畴，使用同一单位构造，再沿 [OpUnopF] 将极限送回。 *)

Program Definition DiagonalAdjunctionColimits
  : HasColimitsOfShape C J
  :=
  {|hasOpLimits :=
      {|hasLimit K :=
          let HC := DiagonalAdjunctionColimit (K^unopF) in
          TransportedLimit (OpUnopF K).1 (OpUnopF K).2
            (HL := @hasOpLimit C J (K^unopF) HC)
      |}
  |}.

End DiagonalAdjunction.

(** Opposite-shape chosen limits and a left adjoint to the ordinary diagonal
    construct each other, without equality of chosen records. *)

(** 反形状选定极限与通常对角函子的左伴随相互构造，不比较选定记录的相等。 *)

Theorem colimits_iff_diagonal_left_adjoint (J C : Cat)
  : HasColimitsOfShape C J ↔ ∃ L : Functor (Fct J C) C, L ⊣ Δ[J,C].
Proof.
  split.
  - intros HC. exists (@ColimitF J C HC). exact (@ColimitAdjunction J C HC).
  - intros [L A]. exact (DiagonalAdjunctionColimits A).
Defined.
