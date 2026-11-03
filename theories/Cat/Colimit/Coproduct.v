From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Coproduct
  Cat.Adjunction
  Cat.Diagram.Dual
  Cat.Colimit.Core
  Cat.Colimit.Shape
  Cat.Limit.Product.
From Cats Require Export
  Cat.Diagram.DualShape.

(** * Binary Coproducts as Discrete Colimits *)

(** * 二元余积作为离散余极限 *)

Section CoproductColimits.
Context {C : Cat} {D : Functor (PairShape^op) C} {S : @Ob C}
    (κ : D ⇒∇ S).

(** A candidate coproduct is a colimit of the opposite discrete pair. *)

(** 候选余积是反离散二点图式的余极限。 *)

Definition coproduct_colimit
    (HC : is_coproduct (D false) (D true) S (κ false) (κ true))
  : is_colimit κ
  := snd (colimit_iff_opposite_limit κ)
      (product_limit (OppositeCone κ) HC).

(** The discrete-pair colimit satisfies the ordinary coproduct property. *)

(** 离散二点余极限满足通常的余积性质。 *)

Definition colimit_coproduct (Hκ : is_colimit κ)
  : is_coproduct (D false) (D true) S (κ false) (κ true)
  := limit_product (OppositeCone κ)
      (fst (colimit_iff_opposite_limit κ) Hκ).

(** Coproduct and colimit properties are equivalent, with no second
    universal-property proof. *)

(** 余积性质与余极限性质等价，不再另证一套泛性质。 *)

Theorem coproduct_iff_colimit
  : is_coproduct (D false) (D true) S (κ false) (κ true)
      ↔ is_colimit κ.
Proof. split; [apply coproduct_colimit | apply colimit_coproduct]. Defined.

End CoproductColimits.

(** Select discrete-pair colimits using opposite product diagram limits. *)

(** 使用反范畴中的积图式极限选择离散二点余极限。 *)

Definition CoproductDiagramColimit {C : Cat} `{HC : !HasCoproduct C}
    (D : Functor (PairShape^op) C)
  : HasColimit C D
  := @OpShapeDiagramColimit PairShape C D
      (@ProductDiagramLimit (C^op) (@hasOpProduct C HC)
        (OppositeDiagram D)).

(** Chosen coproducts supply all opposite discrete-pair colimits. *)

(** 选定余积给出全部反离散二点余极限。 *)

Definition CoproductColimits {C : Cat} `{HC : !HasCoproduct C}
  : HasColimitsOfShape C (PairShape^op)
  := @OpShapeColimits PairShape C
      (@ProductLimits (C^op) (@hasOpProduct C HC)).

(** Recover coproducts through the original pair-limit product recovery. *)

(** 通过原来的二点极限恢复积构造得到余积。 *)

Program Definition PairColimitsCoproduct {C : Cat}
    `{HC : !HasColimitsOfShape C (PairShape^op)}
  : HasCoproduct C
  :=
  {|hasOpProduct := @PairLimitsProduct (C^op)
      (@ColimitsOpShapeLimits PairShape C HC)
  |}.

(** Left adjoints preserve candidate coproducts by opposite product
    preservation. *)

(** 左伴随通过反范畴中积的保持性保持候选余积。 *)

Definition left_adjoint_preserves_coproduct {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {X Y S : @Ob C} {i : Hom X S} {j : Hom Y S}
    (HC : is_coproduct X Y S i j)
  : is_coproduct (F X) (F Y) (F S) (fmap F i) (fmap F j)
  := @right_adjoint_preserves_product (D^op) (C^op)
      (G^opF) (F^opF) (OpAdjunction A) X Y S i j HC.
