From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Pushout
  Cat.Adjunction
  Cat.Colimit.Core
  Cat.Colimit.Shape
  Cat.Limit.Core
  Cat.Limit.Pullback.
From Cats Require Export
  Cat.Diagram.DualShape.

(** * Pushouts as Colimits of Spans *)

(** * 推出作为跨度图式的余极限 *)

Section PushoutColimits.
Context {C : Cat} {D : Fct SpanShape C} {P : @Ob C}
    (κ : D ⇒∇ P).

(** In the span shape, both generating arrows leave [cospan_tip]. Their
    cocone components satisfy the original opposite pullback property. *)

(** 在跨度形状中，两条生成箭头均从 [cospan_tip] 出发；余锥分量满足原反拉回性质。 *)

Definition pushout_colimit
    (HP : is_pushout
      (fmap D (X := cospan_tip) (Y := cospan_left) (path_edge cospan_l))
      (fmap D (X := cospan_tip) (Y := cospan_right) (path_edge cospan_r))
      P (κ cospan_left) (κ cospan_right))
  : is_colimit κ
  := snd (colimit_iff_opposite_limit κ)
      (pullback_limit (OppositeCone κ) HP).

(** A span colimit gives the ordinary candidate pushout property. *)

(** 跨度余极限给出通常的候选推出性质。 *)

Definition colimit_pushout (Hκ : is_colimit κ)
  : is_pushout
      (fmap D (X := cospan_tip) (Y := cospan_left) (path_edge cospan_l))
      (fmap D (X := cospan_tip) (Y := cospan_right) (path_edge cospan_r))
      P (κ cospan_left) (κ cospan_right)
  := limit_pullback (OppositeCone κ)
      (fst (colimit_iff_opposite_limit κ) Hκ).

(** The pushout property is equivalent to the span-colimit property through
    the original pullback/limit characterization. *)

(** 通过原来的拉回／极限刻画，推出性质等价于跨度余极限性质。 *)

Theorem pushout_iff_colimit
  : is_pushout
      (fmap D (X := cospan_tip) (Y := cospan_left) (path_edge cospan_l))
      (fmap D (X := cospan_tip) (Y := cospan_right) (path_edge cospan_r))
      P (κ cospan_left) (κ cospan_right) ↔ is_colimit κ.
Proof. split; [apply pushout_colimit | apply colimit_pushout]. Defined.

End PushoutColimits.

(** Choose the colimit of a specified span from its stored opposite pullback
    limits, using the shared shape adapter. *)

(** 使用共用形状适配，从存储的反范畴拉回极限选择给定跨度的余极限。 *)

Definition PushoutDiagramColimit {C : Cat} `{HP : !HasPushout C}
    (D : Fct SpanShape C)
  : HasColimit C D
  := @OpShapeDiagramColimit CospanShape C D
      (@hasLimit (C^op) CospanShape
        (@PullbackLimits (C^op) (@hasOpPullback C HP)) (OppositeDiagram D)).

(** Select colimits of every span by the original opposite pullback limits.
    This chosen structure must be enabled explicitly. *)

(** 由原反范畴拉回极限选择全部跨度余极限；此选定结构须显式启用。 *)

Definition PushoutColimits {C : Cat} `{HP : !HasPushout C}
  : HasColimitsOfShape C SpanShape
  := @OpShapeColimits CospanShape C
      (@PullbackLimits (C^op) (@hasOpPullback C HP)).

(** Recover selected pushouts with the original cospan-limit recovery. *)

(** 用原来的余跨度极限恢复构造得到选定推出。 *)

Program Definition SpanColimitsPushout {C : Cat}
    `{HC : !HasColimitsOfShape C SpanShape}
  : HasPushout C
  :=
  {|hasOpPullback := @CospanLimitsPullback (C^op)
      (@ColimitsOpShapeLimits CospanShape C HC)
  |}.

(** Left adjoints preserve candidate pushouts by applying opposite
    right-adjoint pullback preservation to the opposite adjunction. *)

(** 将反范畴右伴随保持拉回定理用于反伴随，得到左伴随保持候选推出。 *)

Definition left_adjoint_preserves_pushout {C D : Cat}
    {F : Fct C D} {G : Fct D C} (A : F ⊣ G)
    {X Y Z P : @Ob C} {f : Hom Z X} {g : Hom Z Y}
    {i : Hom X P} {j : Hom Y P} (HP : is_pushout f g P i j)
  : is_pushout (fmap F f) (fmap F g) (F P) (fmap F i) (fmap F j)
  := @right_adjoint_preserves_pullback (D^op) (C^op)
      (G^opF) (F^opF) (OpAdj A) X Y Z P f g i j HP.
