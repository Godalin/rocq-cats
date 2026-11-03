From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Coequalizer
  Cat.Adjunction
  Cat.Diagram.Dual
  Cat.Colimit.Core
  Cat.Colimit.Shape
  Cat.Limit.Equalizer.
From Cats Require Export
  Cat.Diagram.DualShape.

(** * Coequalizers as Parallel-Pair Colimits *)

(** * 余等化子作为平行箭头对的余极限 *)

Section CoequalizerColimits.
Context {C : Cat} {D : Functor (ParallelShape^op) C} {Q : @Ob C}
    (κ : D ⇒∇ Q).

(** In the opposite shape, the arrows run from [true] to [false]. Thus the
    coequalizer projection is the [false] component of the cocone. *)

(** 在反形状中箭头从 [true] 指向 [false]，故余等化子投影是余锥的 [false] 分量。 *)

Definition coequalizer_colimit
    (HC : is_coequalizer
      (fmap D (X := true) (Y := false) (path_edge parallel_l))
      (fmap D (X := true) (Y := false) (path_edge parallel_r)) Q (κ false))
  : is_colimit κ
  := snd (colimit_iff_opposite_limit κ)
      (equalizer_limit (OppositeCone κ) HC).

(** The parallel-pair colimit satisfies the coequalizer property. *)

(** 平行箭头对余极限满足余等化子性质。 *)

Definition colimit_coequalizer (Hκ : is_colimit κ)
  : is_coequalizer
      (fmap D (X := true) (Y := false) (path_edge parallel_l))
      (fmap D (X := true) (Y := false) (path_edge parallel_r)) Q (κ false)
  := limit_equalizer (OppositeCone κ)
      (fst (colimit_iff_opposite_limit κ) Hκ).

(** The coequalizer property is exactly the corresponding colimit property. *)

(** 余等化子性质恰好是相应的余极限性质。 *)

Theorem coequalizer_iff_colimit
  : is_coequalizer
      (fmap D (X := true) (Y := false) (path_edge parallel_l))
      (fmap D (X := true) (Y := false) (path_edge parallel_r)) Q (κ false)
      ↔ is_colimit κ.
Proof. split; [apply coequalizer_colimit | apply colimit_coequalizer]. Defined.

End CoequalizerColimits.

(** Select a parallel-pair colimit using its opposite equalizer diagram. *)

(** 使用反范畴中的等化子图式选择平行箭头对余极限。 *)

Definition CoequalizerDiagramColimit {C : Cat} `{HC : !HasCoequalizer C}
    (D : Functor (ParallelShape^op) C)
  : HasColimit C D
  := @OpShapeDiagramColimit ParallelShape C D
      (@EqualizerDiagramLimit (C^op) (@hasOpEqualizer C HC)
        (OppositeDiagram D)).

(** Chosen coequalizers supply all opposite parallel-pair colimits. *)

(** 选定余等化子给出全部反平行箭头对余极限。 *)

Definition CoequalizerColimits {C : Cat} `{HC : !HasCoequalizer C}
  : HasColimitsOfShape C (ParallelShape^op)
  := @OpShapeColimits ParallelShape C
      (@EqualizerLimits (C^op) (@hasOpEqualizer C HC)).

(** Recover coequalizers with the original parallel-limit recovery. *)

(** 用原来的平行箭头极限恢复构造得到余等化子。 *)

Program Definition ParallelColimitsCoequalizer {C : Cat}
    `{HC : !HasColimitsOfShape C (ParallelShape^op)}
  : HasCoequalizer C
  :=
  {|hasOpEqualizer := @ParallelLimitsEqualizer (C^op)
      (@ColimitsOpShapeLimits ParallelShape C HC)
  |}.

(** Object uniqueness is the original equalizer uniqueness, read backwards. *)

(** 对象唯一性就是反向读取原来的等化子唯一性。 *)

Definition coequalizer_unique {C : Cat} {X Y Q R : @Ob C} {f g : Hom X Y}
    {q : Hom Y Q} {r : Hom Y R}
    (HQ : is_coequalizer f g Q q) (HR : is_coequalizer f g R r)
  : Q ≅[C] R.
Proof.
  pose (e := @equalizer_unique (C^op) Y X R Q f g r q HR HQ).
  exists e.1, e.2.1. split;
    [exact (snd e.2.2) | exact (fst e.2.2)].
Defined.

(** Left adjoints preserve candidate coequalizers by opposite equalizer
    preservation. *)

(** 左伴随通过反范畴中等化子的保持性保持候选余等化子。 *)

Definition left_adjoint_preserves_coequalizer {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {X Y Q : @Ob C} {f g : Hom X Y} {q : Hom Y Q}
    (HC : is_coequalizer f g Q q)
  : is_coequalizer (fmap F f) (fmap F g) (F Q) (fmap F q)
  := @right_adjoint_preserves_equalizer (D^op) (C^op)
      (G^opF) (F^opF) (OpAdjunction A) Y X Q f g q HC.
