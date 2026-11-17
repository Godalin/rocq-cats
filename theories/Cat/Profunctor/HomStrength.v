From Cats Require Export
  Cat.Profunctor.Strength
  Cat.Profunctor.Hom.
From Cats Require Import
  Instance.Set.Core.

Local Open Scope monoidal_scope.
Local Open Scope prof_scope.

(** * The Hom Profunctor Carries Ordinary Context

    Tensoring an arrow with an identity context gives the selected strength
    of Hom. Reuse the functorial Hom transformation and the same monoidal
    context actions; do not construct another tensor or chosen coend. *)

(** * Hom Profunctor 携带通常上下文

    将箭头与恒等上下文张量给出 Hom 的选定强度。复用函子性 Hom 变换及同一幺半
    上下文作用，不另构造张量或选定 coend。 *)

(** ** Hom Strength in Its Actual Bounds

    Fix a monoidal category and value bounds containing its actual Hom
    carrier and equality levels independently. There is no bound on its
    object index and no symmetry or cartesian assumption. *)

(** ** 实际大小界内的 Hom 强度

    固定幺半范畴及独立容纳其真实 Hom 载体／相等层级的值界，不限制对象指标大小，
    也不要求对称性或笛卡尔结构。 *)

Section HomStrength.
Universes o h e s u p.
Context {C : Cat@{o h e s s}} (MC : MonoidalCat C).
Let H
  : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})
  := HomProf C.

(** The original Hom map of the original left-context functor supplies
    naturality in both input and output, without reproving those squares.
    Explicit lifted components keep value bounds separate from the context
    functor's auxiliary respectfulness bounds. *)

(** 原左上下文函子的原 Hom 映射提供输入／输出自然性，不重新证明这些方块。
    显式提升分量让值界与上下文函子的辅助尊重性层级保持分离。 *)

Program Definition HomProfStrengthN (Z : @Ob C)
  : H ⇒ ProfContext MC H Z
  :=
  {|nt XY :=
      {|func h :=
          {|lower := fmap (@BinoidalLeftF C MC Z) (lower h)
          |}
      |}
  |}.
Next Obligation.
  intros f g E. refine {|lower := _|}.
  exact (@fct_fmap_proper C C (@BinoidalLeftF C MC Z)
    _ _ (lower f) (lower g) (lower E)).
Defined.
Next Obligation.
  intros h. refine {|lower := _|}.
  exact (lower (nat_naturality
    (HomProfMapN (@BinoidalLeftF C MC Z)) f h)).
Defined.

(** Choose the Hom strength explicitly; importing this module does not
    register a chosen model instance. Coherence is inherited from the base. *)

(** 显式选取 Hom 强度；导入本模块不注册选定模型实例。相干性继承自基范畴。 *)

Program Definition HomProfStrength
  : HasProfStrength MC H
  :=
  {|prof_strengthN Z := HomProfStrengthN Z
  |}.
Next Obligation.
  intros k. refine {|lower := _|}.
  change ((@id (W ⊗ Y)) ∘ fmap (@BinoidalLeftF C MC W) (lower k) ∘
      (h ⊗m @id X) ≈
    (h ⊗m @id Y) ∘ fmap (@BinoidalLeftF C MC Z) (lower k) ∘
      (@id (Z ⊗ X))).
  rewrite comp_id_l, comp_id_r, !tensor_map_right.
  symmetry. apply monoidal_interchange.
Defined.
Next Obligation.
  intros k. refine {|lower := _|}.
  change (λ⊗[Y] ∘ fmap (@BinoidalLeftF C MC (I⊗[MC])) (lower k) ∘
      (@id (I⊗[MC] ⊗ X)) ≈ (@id Y) ∘ lower k ∘ λ⊗[X]).
  rewrite comp_id_l, comp_id_r.
  exact (premonoidal_unit_l_natural (lower k)).
Defined.
Next Obligation.
  intros k. refine {|lower := _|}.
  change ((@id (Z ⊗ (W ⊗ Y))) ∘
      fmap (@BinoidalLeftF C MC Z)
        (fmap (@BinoidalLeftF C MC W) (lower k)) ∘ α⊗[Z; W; X] ≈
    α⊗[Z; W; Y] ∘ fmap (@BinoidalLeftF C MC (Z ⊗ W)) (lower k) ∘
      (@id ((Z ⊗ W) ⊗ X))).
  rewrite comp_id_l, comp_id_r.
  symmetry. exact (premonoidal_assoc_natural_r Z W (lower k)).
Defined.

(** The transparent action is exactly the original left-context arrow map. *)

(** 透明作用恰为原左上下文箭头映射。 *)

Lemma hom_prof_strength (Z : @Ob C) {X Y : @Ob C} (h : H (X,Y))
  : lower (pstrength[HomProfStrength; Z] h) ≈
      fmap (@BinoidalLeftF C MC Z) (lower h).
Proof. reflexivity. Defined.

End HomStrength.
