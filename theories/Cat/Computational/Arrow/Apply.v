From Cats Require Export
  Cat.Computational.Arrow.Cartesian.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Pure Names for Dynamic Application

    Fix a cartesian Arrow from setoids to a computation category whose
    native hom carrier/equality levels fit the same ambient setoids.
    Computation objects retain their own size. Package pure pairing as a
    value before introducing dynamic application; no exponential is needed. *)

(** * 动态应用的纯命名

    固定从广集到计算范畴的笛卡尔 Arrow，计算原生 Hom 载体／相等层级使用同一
    所在广集界。计算对象保留独立大小。引入动态应用前，先将纯配对打包为值；
    不要求指数。 *)

Section PureNames.
Universes o u p.
Context {K : Cat@{o u p _ _}}
    (A : Arrow (SetCat@{u p _ _ _ _ _}) K
      (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct)).

(** Name the pure arrow that pairs a fixed value with its ordinary input.
    Both the ordinary value and the resulting computation use specified
    equality. *)

(** 命名将固定值与通常输入配对的纯箭头；通常值及所得计算均使用指定相等。 *)

Program Definition arrow_apply_pair (X Y : SetC@{u p})
  : X →r HomSet (A Y) (A (X ×S Y))
  :=
  {|func x := arr[A; ⟨const_resp Y x, id⟩]
  |}.
Next Obligation.
  intros x x' H. apply functor_fmap_proper. intros y.
  split; [exact H | reflexivity].
Defined.

End PureNames.

(** * Arrows with Dynamic Application

    Work over the same setoid base, keeping native computation homs as
    ordinary values. Extend one cartesian Arrow by application and the
    three Control.Arrow laws: pure pairing, computation substitution on
    the input, and computation postcomposition. Inverse representations
    and a recovered Monad are derived questions, not extra class fields. *)

(** * 带动态应用的 Arrow

    在同样的广集基底上，将原生计算 Hom 作为通常值。为一个笛卡尔 Arrow 增加
    应用及 Control.Arrow 的三条定律：纯配对、输入计算代入及计算后合成。
    逆向表示与回收 Monad 属于导出问题，不另存为类字段。 *)

Section Interface.
Universes o u p.
Context (K : Cat@{o u p _ _}).

Class ArrowApply
  :=
  (** The unique immediate parent supplies pure arrows and context. *)

  (** 唯一直接父结构提供纯箭头与上下文。 *)

  { ArrowApplyA :> Arrow (SetCat@{u p _ _ _ _ _}) K
      (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct)

  (** Run the computation supplied in the first input on the second input.
      Computations are values in their native Hom setoid. *)

  (** 将第一输入提供的计算运行于第二输入；计算是其原生 Hom 广集中的值。 *)

  ; arrow_apply {X Y : SetC@{u p}}
    : Hom (ArrowApplyA (HomSet (ArrowApplyA X) (ArrowApplyA Y) ×S X))
        (ArrowApplyA Y)

  (** Applying a dynamically named pure pairing leaves both inputs intact. *)

  (** 应用动态命名的纯配对，保留两个输入。 *)

  ; arrow_apply_pair_id (X Y : SetC@{u p})
    : arrow_apply ∘ arr[ArrowApplyA;
        arrow_apply_pair ArrowApplyA X Y × id_resp (X := Y)] ≈ id

  (** Moving an input computation into the supplied computation preserves
      execution order. The context contains that computation as a value. *)

  (** 将输入计算移入所给计算，保持执行次序；上下文将该计算作为值携带。 *)

  ; arrow_apply_pre {X Y Z : SetC@{u p}}
      (g : Hom (ArrowApplyA X) (ArrowApplyA Y))
    : arrow_apply ∘ arr[ArrowApplyA;
        (comp_r_resp (Z := ArrowApplyA Z) (f := g)) × id_resp (X := X)] ≈
      arrow_apply ∘ context[ArrowApplyA;
        HomSet (ArrowApplyA Y) (ArrowApplyA Z); g]

  (** Postcomposing the supplied computation agrees with postcomposing
      the result of dynamic application. *)

  (** 后合成所给计算，等于后合成动态应用的结果。 *)

  ; arrow_apply_post {X Y Z : SetC@{u p}}
      (h : Hom (ArrowApplyA Y) (ArrowApplyA Z))
    : arrow_apply ∘ arr[ArrowApplyA;
        (comp_l_resp (X := ArrowApplyA X) (f := h)) × id_resp (X := X)] ≈
      h ∘ arrow_apply
  }.

End Interface.

Arguments ArrowApplyA {_} _.
Arguments arrow_apply {_} _ {_ _}.
Arguments arrow_apply_pair_id {_} _ _ _.
Arguments arrow_apply_pre {_} _ {_ _ _} _.
Arguments arrow_apply_post {_} _ {_ _ _} _.

Notation "'apply[' A ';' X ';' Y ']'" := (arrow_apply A (X := X) (Y := Y))
  : computation_scope.


(** * Applying a Fixed Computation

    Fix an ArrowApply at the same native setoid bounds. Derive the law
    that applying a fixed computation as a value returns that computation.
    Only the three supplied laws and ordinary Arrow equations are used;
    equality of computations is never reduced to pointwise testing. *)

(** * 应用固定计算

    固定同样原生广集界上的 ArrowApply，导出将固定计算作为值应用时返回原计算
    的定律。仅使用所给三条定律及通常 Arrow 方程，不将计算相等化为逐点测试。 *)

Section Fixed.
Universes o u p.
Context {K : Cat@{o u p _ _}} (AA : ArrowApply K).

(** Supply a fixed computation together with the current ordinary input. *)

(** 将固定计算与当前通常输入一起提供。 *)

Definition arrow_apply_const {X Y : SetC@{u p}} (f : Hom (AA X) (AA Y))
  : Hom (AA X) (AA Y)
  := apply[AA; X; Y] ∘ arr[AA; ⟨const_resp X f, id⟩].

(** Supplying equal computations preserves native computation equality. *)

(** 提供相等计算保持原生计算相等。 *)

Global Instance arrow_apply_const_proper {X Y : SetC@{u p}}
  : Proper (HomEq ==> HomEq) (@arrow_apply_const X Y).
Proof.
  intros f g H. unfold arrow_apply_const.
  apply comp_proper; [reflexivity |]. apply functor_fmap_proper.
  intros x. split; [exact H | reflexivity].
Qed.

(** Postcomposition can be performed inside or after fixed application. *)

(** 后合成可在固定应用内部或之后进行。 *)

Lemma arrow_apply_const_post {X Y Z : SetC@{u p}}
    (f : Hom (AA X) (AA Y)) (h : Hom (AA Y) (AA Z))
  : arrow_apply_const (h ∘ f) ≈ h ∘ arrow_apply_const f.
Proof.
  unfold arrow_apply_const.
  transitivity ((apply[AA; X; Z] ∘
    arr[AA; comp_l_resp (f := h) × id_resp]) ∘
      arr[AA; ⟨const_resp X f, id⟩]).
  - rewrite comp_assoc, <- functor_comp. apply comp_proper;
      [reflexivity |]. apply functor_fmap_proper. intros x.
    split; reflexivity.
  - rewrite arrow_apply_post, comp_assoc. reflexivity.
Qed.

(** The pairing law and pure projection recover identity application. *)

(** 由配对律和纯投影得到恒等计算的应用。 *)

Lemma arrow_apply_const_id (X : SetC@{u p})
  : arrow_apply_const (@id (AA X)) ≈ id.
Proof.
  pose (j := (⟨@const_resp X UnitS tt, id⟩ : X →r (UnitS ×S X))).
  pose (q := (π2 : (UnitS ×S X) →r X)).
  assert (Hj : arrow_apply_const arr[AA; j] ≈ arr[AA; j]).
  { unfold arrow_apply_const.
    transitivity ((apply[AA; X; UnitS ×S X] ∘
      arr[AA; arrow_apply_pair AA UnitS X × id_resp]) ∘ arr[AA; j]).
    - rewrite comp_assoc, <- functor_comp. apply comp_proper;
        [reflexivity |]. apply functor_fmap_proper. intros x.
      split; reflexivity.
    - rewrite arrow_apply_pair_id, comp_id_l. reflexivity. }
  assert (Hqj : arr[AA; q] ∘ arr[AA; j] ≈ @id (AA X)).
  { rewrite <- functor_comp. transitivity (arr[AA; id_resp (X := X)]).
    - apply functor_fmap_proper. intros x. reflexivity.
    - apply functor_id. }
  transitivity (arrow_apply_const (arr[AA; q] ∘ arr[AA; j])).
  - apply arrow_apply_const_proper. symmetry. exact Hqj.
  - rewrite arrow_apply_const_post, Hj. exact Hqj.
Qed.

(** Dynamic application of a fixed arrow is that arrow in native Hom equality. *)

(** 动态应用固定箭头，在原生 Hom 相等下就是该箭头。 *)

Lemma arrow_apply_const_value {X Y : SetC@{u p}}
    (f : Hom (AA X) (AA Y))
  : arrow_apply_const f ≈ f.
Proof.
  transitivity (arrow_apply_const (f ∘ @id (AA X))).
  - apply arrow_apply_const_proper. symmetry. apply comp_id_r.
  - rewrite arrow_apply_const_post, arrow_apply_const_id, comp_id_r.
    reflexivity.
Qed.

End Fixed.
