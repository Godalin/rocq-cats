From Cats Require Export
  Cat.Computational.Freyd.Context
  Cat.Computational.Arrow.Core.
From Cats Require Import
  Cat.Monoidal.Cartesian.

Local Open Scope computation_scope.

(** * Reconstructing Computational Arrows

    Pure inclusion and the transported left action recover Arrow. The
    computation category is the actual value-indexed Freyd category, not
    an assertion about unused ambient objects. All laws reuse the general
    boundary equations, with no new coherence assumptions. *)

(** * 重建计算 Arrow

    纯嵌入及运输后的左作用恢复 Arrow。计算范畴为实际按值索引的 Freyd
    范畴，不主张涉及未使用的环境对象。全部定律复用一般边界方程，不增加
    相干假设。 *)

Section Reconstruction.
Context {C K : Cat} (F : FreydCat C K).
Let CC
  : CartesianCat C
  := @hasCartesian C K F.
Local Existing Instance CC.
Let D
  : Cat
  := FreydComputations F.

(** The reconstructed action is conjugation by the selected tensor
    boundaries. Its witnesses and inverse boundary maps stay transparent. *)

(** 重建作用为沿选定张量边界的共轭，其见证及反向边界映射保持透明。 *)

Program Definition FreydArrow
  : Arrow C D (@CartesianMonoidal C hasTerminal hasProduct)
  :=
  {|ArrowF := FreydPureF F
  ; arrow_context X Y Z f := freyd_context F Z f
  ; arrow_context_proper X Y Z :=
      @functor_fmap_proper D D (FreydContextF F Z) X Y
  ; arrow_context_comp X Y W Z g f :=
      @functor_comp D D (FreydContextF F Z) X Y W g f
  |}.
Next Obligation.
  etransitivity; [exact (freyd_context_pure F Z f) |].
  pose proof (@cartesian_tensor_map C hasTerminal hasProduct
    Z Z X Y (@id Z) f) as H. symmetry in H.
  exact (@functor_fmap_proper C K F _ _ _ _ H).
Defined.
Next Obligation.
  pose proof (freyd_context_natural F f h) as H.
  rewrite <- !cartesian_tensor_map in H. exact H.
Defined.
Next Obligation. exact (freyd_context_unit F f). Defined.
Next Obligation. exact (freyd_context_assoc F Z W f). Defined.

End Reconstruction.
