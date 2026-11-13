From Cats Require Export
  Cat.Applicative.Core
  Cat.Computational.Arrow.Global.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product.
From Cats.Set Require Import
  Constant.

Local Open Scope computation_scope.
Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * Applicative Values of an Arrow on Setoids

    Fix an Arrow from setoids into a computation category. Require its hom
    carrier and equality levels to match the ambient setoid levels. Global
    computations then form an endofunctor, and pure constants extend the
    already constructed lax structure to an Applicative. No Monad or
    exponential structure is required, and no chosen model is enabled. *)

(** * 广集上 Arrow 的 Applicative 值

    固定从广集进入计算范畴的 Arrow，要求其 Hom 载体及相等层级对应所在广集
    层级。全局计算于是组成自函子，纯常值将已有 lax 结构扩充为 Applicative。
    不要求 Monad 或指数结构，也不启用选定模型。 *)

Section SetBase.
Universes o u p.
Context (K : Cat@{o u p _ _})
    (A : Arrow (SetCat@{u p _ _ _ _ _}) K
      (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct)).

(** Embed a setoid value as the pure constant computation from the
    singleton. Respectfulness compares constants pointwise. *)

(** 将广集值嵌入为从单元素广集出发的纯常值计算；尊重性逐点比较常值映射。 *)

Program Definition arrow_value_pure (X : SetC@{u p})
  : X →r ArrowGlobalF A X
  :=
  {|func x := arr[A; const_resp UnitS x]
  |}.
Next Obligation.
  intros x y H. apply functor_fmap_proper. intros z. exact H.
Defined.

(** Pure constant computations are natural in ordinary respectful maps. *)

(** 纯常值计算关于通常保相等映射自然。 *)

Program Definition ArrowValuePureN
  : IdF ⇒ ArrowGlobalF A
  :=
  {|nt X := arrow_value_pure X
  |}.
Next Obligation.
  intros x.
  change (arr[A; const_resp UnitS (f x)] ≈
    arr[A; f] ∘ arr[A; const_resp UnitS x]).
  rewrite <- functor_comp. apply functor_fmap_proper. intros z. reflexivity.
Defined.

(** The generic global-computation lax functor is an endofunctor here.
    Pure constants preserve its unit and pairing. The computation hom
    carrier/equality levels match the selected ambient setoid levels. *)

(** 一般全局计算 lax 函子在此为自函子；纯常值保持其单位和配对。计算 Hom 的
    载体／相等层级与选定所在广集层级对应。 *)

Program Definition ArrowA
  : Applicative SetCat SetCat_HasTerminal SetCat_HasProduct
  :=
  {|ApplicativeLax := ArrowGlobalLax A
  ; applicative_pure := ArrowValuePureN
  |}.
Next Obligation.
  intros x. change (arr[A; const_resp UnitS x] ≈ @id (A UnitS)).
  transitivity (arr[A; (id_resp (X := UnitS))]).
  - apply functor_fmap_proper. intros z. exact tt.
  - exact (arrow_arr_id A UnitS).
Defined.
Next Obligation.
  intros [x y]. change (arr[A; const_resp UnitS (x,y)] ≈
    arr[A; const_resp UnitS x] &&&[A] arr[A; const_resp UnitS y]).
  rewrite arrow_fanout_pure. apply functor_fmap_proper. intros z.
  split; reflexivity.
Defined.

(** Binary lifting is precisely actual ordered fanout followed by the
    pure binary operation. This exposes the semantic operation without
    unfolding the Applicative packaging in clients. *)

(** 二元提升恰为实际有序 fanout 后接纯二元运算，使客户端无需展开
    Applicative 打包即可使用其语义运算。 *)

Lemma arrow_a_lift2 {X Y Z : SetC@{u p}} (h : X ×S Y →r Z)
    (f : ArrowGlobalF A X) (g : ArrowGlobalF A Y)
  : lift₂[ArrowA; h] (f,g) ≈S arr[A; h] ∘ (f &&&[A] g).
Proof. reflexivity. Qed.

End SetBase.
