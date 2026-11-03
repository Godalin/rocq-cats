From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Diagram.Dual
  Cat.Diagram.Reindex
  Cat.Limit.Reindex
  Cat.Limit.Core
  Cat.Colimit.Core.

(** * Reading Dual Shapes without Double Opposition *)

(** * 去除对偶形状中的双重取反 *)

(** An opposite-shape diagram becomes a diagram on the original shape in
    the opposite target. The identity functor only adapts its source. *)

(** 反形状图式成为原形状在反目标范畴中的图式；恒等函子仅适配其源。 *)

Definition OppositeDiagram {J C : Cat} (D : Functor (J^op) C)
  : Functor J (C^op)
  := D^opF ∘F ToDoubleOpF.

(** Restrict the stored opposite cone along the double-opposite inclusion. *)

(** 沿双重反范畴嵌入限制存储的反锥。 *)

Definition OppositeCone {J C : Cat} {D : Functor (J^op) C} {X}
    (κ : D ⇒∇ X)
  : X ⇒Δ OppositeDiagram D
  := op_cone κ ∘Δ ToDoubleOpF.

(** The existing full, essentially surjective reindexing theorem removes
    double opposition from the universal property. *)

(** 已有的满且本质满重索引定理从泛性质中去除双重取反。 *)

Theorem colimit_iff_opposite_limit {J C : Cat}
    {D : Functor (J^op) C} {X} (κ : D ⇒∇ X)
  : is_colimit κ ↔ is_limit (OppositeCone κ).
Proof.
  exact (limit_iff_restrict to_double_op_full
    to_double_op_essentially_surjective (op_cone κ)).
Defined.

(** Extend a chosen original-shape opposite limit to the stored dual shape.
    This reuses general limit reindexing, including its mediator. *)

(** 将原形状中的选定反范畴极限延拓到存储的对偶形状；中介也复用一般极限重索引。 *)

Program Definition OpShapeDiagramColimit {J C : Cat}
    (D : Functor (J^op) C)
    `{HL : !HasLimit (C^op) (OppositeDiagram D)}
  : HasColimit C D
  :=
  {|hasOpLimit := ReindexedLimit to_double_op_full
      to_double_op_essentially_surjective (D^opF)
  |}.

(** Original-shape limits in the opposite category select opposite-shape
    colimits. The structure is opt-in. *)

(** 反范畴中的原形状极限选择反形状余极限；该结构须显式启用。 *)

Program Definition OpShapeColimits {J C : Cat}
    `{HL : !HasLimitsOfShape (C^op) J}
  : HasColimitsOfShape C (J^op)
  :=
  {|hasOpLimits := ReindexedLimits to_double_op_full
      to_double_op_essentially_surjective
  |}.

(** Conversely, read selected opposite-shape colimits as original-shape
    limits in the opposite category. *)

(** 反向将选定反形状余极限读作反范畴中的原形状极限。 *)

Definition ColimitsOpShapeLimits {J C : Cat}
    `{HC : !HasColimitsOfShape C (J^op)}
  : HasLimitsOfShape (C^op) J
  := @ReindexedLimits (J^op^op) J (C^op) FromDoubleOpF
      from_double_op_full from_double_op_essentially_surjective
      (@hasOpLimits C (J^op) HC).
