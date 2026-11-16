From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Pullback
  Cat.Induced
  Cat.Natural
  Cat.Pullback
  Instance.Set.Core
  Instance.Set.Pullback.
From CatsTests Require Import
  Gluing.

(** * Pointwise Pullback Interfaces and Computation

    The indexing and target categories keep independent object and law
    bounds. Concrete tests use a diagram with all respectful endomorphisms,
    rather than a constant diagram, and retain Boolean equality witnesses. *)

(** * 逐点拉回接口与计算

    索引和目标范畴保持独立的对象及定律界。具体测试的图式包含所有保相等
    自同态，而非常值图式，并保留布尔相等见证。 *)

(** ** Target Equality below Arrows

    Fix unrelated indexing and target size profiles; the index objects
    may be larger than target objects without enlarging component values. *)

(** ** 目标相等低于箭头

    固定不相干的索引与目标大小配置；索引对象可大于目标对象，无需扩大分量值。 *)

Section LowEquality.
Universes oj hj ej lj oc hc ec lc.
Constraint ec < hc.
Constraint hc < oc.
Constraint oc < oj.
Constraint oj < lj.
Constraint oc < lc.
Context (J : Cat@{oj hj ej lj lj}) (C : Cat@{oc hc ec lc lc}).
Context `{HPb : !HasPullback C}.

(** Selection preserves the target's native arrow/equality separation. *)

(** 选择保持目标原有的箭头与相等层级分离。 *)

Definition low_eq_pointwise_pullbacks
  : HasPullback (FctCat J C)
  := FctCat_HasPullback J C.

End LowEquality.

(** ** Target Equality above Arrows

    Reverse the strict arrow/equality order and the object-size order.
    The candidate interface also needs no globally chosen target pullbacks. *)

(** ** 目标相等高于箭头

    反转箭头与相等的严格次序及对象大小次序。候选接口也不需要全局选定目标拉回。 *)

Section HighEquality.
Universes oj hj ej lj oc hc ec lc.
Constraint hc < ec.
Constraint ec < oc.
Constraint oj < oc.
Constraint oj < lj.
Constraint oc < lc.
Context (J : Cat@{oj hj ej lj lj}) (C : Cat@{oc hc ec lc lc}).

(** This cone is universal using only the supplied component properties. *)

(** 仅使用给定分量性质，此锥就是泛锥。 *)

Definition high_eq_candidate {F G H P : Fct J C}
    (α : F ⇒ H) (β : G ⇒ H) (p : P ⇒ F) (q : P ⇒ G)
    (HP : ∀ i, is_pullback (α i) (β i) (P i) (p i) (q i))
  : is_pullback (C := FctCat J C) α β P p q
  := pointwise_pullback_universal α β p q HP.

(** An explicitly supplied choice can be lifted at the reversed levels. *)

(** 在反向层级下也可提升显式提供的选择。 *)

Definition high_eq_pointwise_pullbacks `{HPb : !HasPullback C}
  : HasPullback (FctCat J C)
  := FctCat_HasPullback J C.

End HighEquality.

(** ** A Setoid-Valued Diagram with Nonconstant Arrow Action

    Two labels name the same tagged setoid, with every respectful map as
    an indexing arrow. The inclusion diagram applies that arrow unchanged.
    Enable only the target pullbacks within this section. *)

(** ** 箭头作用非常值的广集值图式

    两个标签都指定同一带标签广集，每个保相等映射都是索引箭头；包含图式保持
    该箭头不变。只在本节启用目标拉回选择。 *)

Section TaggedDiagram.
Local Existing Instance SetCat_HasPullback.

(** Use the existing induced-category inclusion, without a new category. *)

(** 使用已有诱导范畴的包含，无需另建范畴。 *)

Definition TaggedDiagram
  : Fct (InducedCat bool (λ _, TaggedGluingS)) SetCat
  := InducedInclusionF bool (λ _, TaggedGluingS).

(** The identity cospan has the selected pointwise pullback diagram. *)

(** 恒等余跨度具有选定的逐点拉回图式。 *)

Definition TaggedPullbackDiagram
  : Fct (InducedCat bool (λ _, TaggedGluingS)) SetCat
  := PointwisePullbackF (idN (F := TaggedDiagram)) idN.

(** A pullback element retains both representations and their equality data. *)

(** 拉回元素保留两个表示及它们的相等数据。 *)

Definition tagged_pullback_element
  : TaggedPullbackDiagram false
  := ((3%nat, false); ((3%nat, true); (eq_refl, true))).

(** The first coordinate really runs the nontrivial indexing arrow. *)

(** 第一坐标实际执行非平凡的索引箭头。 *)

Example tagged_pullback_map_first_computes
  : (fmap TaggedPullbackDiagram (X := false) (Y := true)
      gluing_toggle tagged_pullback_element).1 = (3%nat, true).
Proof. reflexivity. Qed.

(** The other coordinate changes its own representation independently. *)

(** 另一坐标独立地改变自身表示。 *)

Example tagged_pullback_map_second_computes
  : (fmap TaggedPullbackDiagram (X := false) (Y := true)
      gluing_toggle tagged_pullback_element).2.1 = (3%nat, false).
Proof. reflexivity. Qed.

(** Equality ignores the changed tags, without erasing its Boolean evidence. *)

(** 相等忽略已改变的标签，同时不擦除其布尔证据。 *)

Example tagged_pullback_map_equal
  : fmap TaggedPullbackDiagram (X := false) (Y := true)
      gluing_toggle tagged_pullback_element ≈S tagged_pullback_element.
Proof. split; exact (eq_refl, true). Defined.

(** Equal indexing maps induce equal actions, even with different tags. *)

(** 即使标签不同，相等的索引映射也诱导相等的作用。 *)

Example tagged_pullback_index_equal
  : fmap TaggedPullbackDiagram (X := false) (Y := true) gluing_toggle ≈
      fmap TaggedPullbackDiagram (X := false) (Y := true) id_resp.
Proof.
  apply functor_fmap_proper. intros [n b]. exact (eq_refl, true).
Defined.

(** The mapped commuting-square witness remains accessible data; no native
    computation of an abstract proof field is asserted. *)

(** 映射后的交换方形见证仍是可访问数据；不声称抽象证明字段原生计算。 *)

Definition tagged_pullback_square_token
  : bool
  := snd ((fmap TaggedPullbackDiagram (X := false) (Y := true)
      gluing_toggle tagged_pullback_element).2.2).

(** The candidate mediator reuses the original component pullback pair. *)

(** 候选中介复用原分量拉回配对。 *)

Definition TaggedDiagonalN
  : TaggedDiagram ⇒ TaggedPullbackDiagram
  := PointwisePullbackLiftN (idN (F := TaggedDiagram)) idN
      (PointwisePullbackFstN idN idN) (PointwisePullbackSndN idN idN)
      (λ _, pullback_universal) idN idN (λ _, reflexivity _).

(** The first mediator projection computes on the supplied argument. *)

(** 中介的第一投影在给定实参上计算。 *)

Example tagged_diagonal_first_computes
  : (TaggedDiagonalN false (4%nat, true)).1 = (4%nat, true).
Proof. reflexivity. Qed.

(** The second mediator projection computes independently. *)

(** 中介的第二投影独立计算。 *)

Example tagged_diagonal_second_computes
  : (TaggedDiagonalN true (5%nat, false)).2.1 = (5%nat, false).
Proof. reflexivity. Qed.

End TaggedDiagram.

(** ** Presheaf Use with Explicit Size Bounds

    Setoid pullbacks store equality witnesses, so their equality bound
    must fit the value carrier bound. The indexing category may still be
    larger. This does not construct presheaf exponentials or a gluing CCC. *)

(** ** 带显式大小界的预层应用

    广集拉回保存相等见证，因此相等界必须容纳于值载体界。索引范畴仍可更大。
    这里尚未构造预层指数或粘合 CCC。 *)

Section PresheafUse.
Universes u p oj hj ej lj.
Constraint p < u.
Constraint u < oj.
Context (J : Cat@{oj hj ej lj lj}).

(** Explicitly chosen setoid pullbacks lift to contravariant diagrams. *)

(** 显式选定的广集拉回提升到反变图式。 *)

Definition presheaf_pointwise_pullbacks
  : HasPullback (FctCat (J^op) SetCat@{u p _ _ _ _ _})
  := @FctCat_HasPullback _ _ SetCat_HasPullback.

End PresheafUse.
