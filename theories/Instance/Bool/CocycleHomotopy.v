From Cats Require Export
  Instance.Bool.CocycleSphereCylinder
  Instance.Set.Simplicial.Cocycle.Nerve.
From Cats Require Import
  Cat.Core
  Cat.Natural.

Import Cats.Instance.Set.Groupoid (EqGpd).
Import Cats.Instance.Set.Simplicial.Vertex.Core (VertexNerve).

Local Existing Instance BoolS_Monoid.
Local Open Scope nat_scope.

(** * The Boolean Model Cannot Retract through an Ordinary Nerve

    A sphere coefficient survives homotopies of maps, even when the maps
    do not fix a chosen basepoint: every edge of this target is constant.
    The general obstruction in
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Nerve.cocycle no nerve homotopy retract}
    {%[cocycle_no_nerve_homotopy_retract]%}% now applies to the coefficient
    true, which differs from the unit false.

    Thus no maps to an ordinary category nerve and back can have their
    round trip linked to the identity by a finite chain of actual cylinder
    homotopies, reversed steps and natural equalities. A homotopy
    equivalence given by such maps is excluded. This does not yet exclude
    zigzags of weak equivalences or classify all 1-types; those require
    further comparison and invariance theorems. *)

(** * 布尔模型不能经普通 Nerve 同伦收缩

    即使映射不固定选定基点，映射同伦也保留球面系数，因为此目标的每条边均
    为常值。一般障碍
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Nerve.cocycle no nerve homotopy retract}
    {%[cocycle_no_nerve_homotopy_retract]%}% 因而适用于系数真，它与单位假
    不同。

    因此，不存在到普通范畴 nerve 再返回的映射，使往返经有限次实际柱同伦、
    反向步及自然相等联系到恒等映射。这排除了由这种映射给出的同伦等价。
    尚未排除弱等价的之字形链，也未分类所有 1-types；这些仍需进一步比较及
    不变性定理。 *)

(** ** Actual Maps to Any Presented Category Nerve

    Fix any object presentation and two actual simplicial maps, at
    independent ambient carrier and equality bounds. No groupoid or Kan
    assumption is needed for the ordinary category. *)

(** ** 到任意呈现范畴 Nerve 的实际映射

    固定任意对象呈现及两个实际单纯映射，环境载体与相等界独立。普通范畴不需
    群胚或 Kan 假设。 *)

Section BooleanNerveRetraction.
Universes u p.
Context {A : SetC} {C : Cat} (T : Functor (EqGpd A) C).

Let B
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(BoolS).

Let N
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := VertexNerve T.

Context (f : B ⇒ N) (g : N ⇒ B).

(** The generated relation includes either orientation of every cylinder
    homotopy, but it cannot equate this round trip with the identity. *)

(** 生成关系包含每份柱同伦的两个方向，但无法将此往返与恒等映射等同。 *)

Definition bool_cocycle_no_nerve_homotopy_retract
  : ¬ (g ∘Nv f : @CocycleHomotopyMapS BoolS BoolS_Monoid B) ≈S idN.
Proof.
  apply (cocycle_no_nerve_homotopy_retract T f g true).
  intros E. discriminate E.
Defined.

(** In particular, a single forward cylinder cannot give the retraction. *)

(** 特别地，单个正向柱不能给出该收缩。 *)

Definition bool_cocycle_no_nerve_forward_homotopy
  : ¬ SimplicialHomotopy (g ∘Nv f) idN.
Proof.
  intros H. apply bool_cocycle_no_nerve_homotopy_retract.
  exact (cocycle_homotopy_map_step H).
Defined.

(** The opposite orientation is also excluded by reversing its retained
    chain witness, without constructing an interval reversal. *)

(** 反向柱也被排除：反转其保留链见证即可，无须构造区间反转。 *)

Definition bool_cocycle_no_nerve_backward_homotopy
  : ¬ SimplicialHomotopy idN (g ∘Nv f).
Proof.
  intros H. apply bool_cocycle_no_nerve_homotopy_retract.
  symmetry. exact (cocycle_homotopy_map_step H).
Defined.

End BooleanNerveRetraction.
