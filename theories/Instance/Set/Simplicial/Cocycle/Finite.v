From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Low.
From Cats Require Import
  Cat.Chain.
From Stdlib Require Import
  Lia.

Local Open Scope monoid_scope.
Local Open Scope ordinal_scope.

(** * Finite Triangle Tables

    In dimensions three and four, list the strictly increasing triangle
    labels. Repeated positions receive the unit. The only additional laws
    are the tetrahedron equations on four distinct positions. *)

(** * 有限三角形标签表

    在三、四维中列出严格递增的三角形标签，重复位置取单位。额外定律恰为
    四个不同位置上的四面体方程。 *)

(** ** A Tetrahedron and a Four-Simplex

    Fix a coefficient monoid. No group or commutativity is needed to store
    a table once its tetrahedron equations have been supplied. *)

(** ** 四面体与四维单形

    固定系数幺半群。给定四面体方程后，保存标签表不要求群结构或交换性。 *)

Section Tables.
Context {M : SetC} `{HM : !Monoid M}.

(** Assign the 4 increasing triangles their coefficients. *)

(** 为 4 个递增三角形赋系数。 *)

Definition TetrahedronLabel (p q r s : M)
    (x y z : Ordinal 3)
  : M
  := match fin_rank x, fin_rank y, fin_rank z with
     | 0, 1, 2 => p
     | 0, 2, 3 => q
     | 1, 2, 3 => r
     | 0, 1, 3 => s
     | _, _, _ => 1
     end.

(** The listed tetrahedron equations extend the table to a whole cocycle. *)

(** 列出的四面体方程将标签表延伸为整个 cocycle。 *)

Program Definition TetrahedronTwoCocycle (p q r s : M)
    (H0 : p ⋅ q ≈S r ⋅ s)
  : TwoCocycle [Ord 3] M
  :=
  {|two_cocycle_triangle x y z u v :=
      TetrahedronLabel p q r s x y z
  |}.
Next Obligation. intros u u' Hu v v' Hv. reflexivity. Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | [[] | []]]]],
    y as [[] | [[] | [[] | [[] | []]]]]; reflexivity.
Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | [[] | []]]]],
    y as [[] | [[] | [[] | [[] | []]]]]; reflexivity.
Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | [[] | []]]]], y as [[] | [[] | [[] | [[] | []]]]],
    z as [[] | [[] | [[] | [[] | []]]]], w as [[] | [[] | [[] | [[] | []]]]];
    cbn in *; try solve [destruct f | destruct g | destruct h];
    rewrite ?monoid_unit_l, ?monoid_unit_r; try reflexivity;
    assumption.
Defined.

(** Assign the 10 increasing triangles their coefficients. *)

(** 为 10 个递增三角形赋系数。 *)

Definition PentachoronLabel (a b c d e f g h i j : M)
    (x y z : Ordinal 4)
  : M
  := match fin_rank x, fin_rank y, fin_rank z with
     | 0, 1, 2 => a
     | 0, 1, 3 => b
     | 0, 1, 4 => c
     | 0, 2, 3 => d
     | 0, 2, 4 => e
     | 0, 3, 4 => f
     | 1, 2, 3 => g
     | 1, 2, 4 => h
     | 1, 3, 4 => i
     | 2, 3, 4 => j
     | _, _, _ => 1
     end.

(** The listed tetrahedron equations extend the table to a whole cocycle. *)

(** 列出的四面体方程将标签表延伸为整个 cocycle。 *)

Program Definition PentachoronTwoCocycle (a b c d e f g h i j : M)
    (H0 : g ⋅ i ≈S j ⋅ h)
    (H1 : d ⋅ f ≈S j ⋅ e)
    (H2 : b ⋅ f ≈S i ⋅ c)
    (H3 : a ⋅ e ≈S h ⋅ c)
    (H4 : a ⋅ d ≈S g ⋅ b)
  : TwoCocycle [Ord 4] M
  :=
  {|two_cocycle_triangle x y z u v :=
      PentachoronLabel a b c d e f g h i j x y z
  |}.
Next Obligation. intros u u' Hu v v' Hv. reflexivity. Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | [[] | [[] | []]]]]],
    y as [[] | [[] | [[] | [[] | [[] | []]]]]]; reflexivity.
Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | [[] | [[] | []]]]]],
    y as [[] | [[] | [[] | [[] | [[] | []]]]]]; reflexivity.
Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | [[] | [[] | []]]]]],
    y as [[] | [[] | [[] | [[] | [[] | []]]]]],
    z as [[] | [[] | [[] | [[] | [[] | []]]]]], w as [[] | [[] | [[] | [[] | [[] | []]]]]];
    cbn in *; try solve [destruct f0 | destruct g0 | destruct h0];
    rewrite ?monoid_unit_l, ?monoid_unit_r; try reflexivity;
    assumption.
Defined.

End Tables.

(** ** Reading the Faces of a Tetrahedron

    Two tetrahedron cocycles agree when their four increasing face labels
    agree. Repeated-position labels are already fixed by normalization. *)

(** ** 读取四面体的面

    两个四面体 cocycle 的四个递增面标签若相等，则整个 cocycle 相等。
    重复位置的标签已由归一化确定。 *)

Section TetrahedronEquality.
Context {M : SetC} `{HM : !Monoid M}.

(** Face coefficients suffice; no equality of record fields is required. *)

(** 面系数已经足够，无须记录字段的原生相等。 *)

Lemma tetrahedron_cocycle_eq (c d : TwoCocycle [Ord 3] M)
    (H : ∀ j : Ordinal 3,
      ordinal_cocycle_triangle_value (TwoCocyclePullback δ[2; j] c) ≈S
      ordinal_cocycle_triangle_value (TwoCocyclePullback δ[2; j] d))
  : TwoCocycleEq c d.
Proof.
  intros x y z f g.
  destruct x as [[] | [[] | [[] | [[] | []]]]],
    y as [[] | [[] | [[] | [[] | []]]]],
    z as [[] | [[] | [[] | [[] | []]]]];
    cbn in f, g; destruct f, g;
    try solve [transitivity (1 : M);
      [first [apply two_cocycle_unit_l | apply two_cocycle_unit_r]
      | symmetry; first [apply two_cocycle_unit_l | apply two_cocycle_unit_r]]];
    first [exact (H fin_first) | exact (H (fin_first⁺)) |
      exact (H (fin_first⁺⁺)) |
      exact (H (fin_first⁺⁺⁺))].
Defined.

End TetrahedronEquality.

(** Two actual triangles are equal if their increasing coefficients agree;
    the two round trips from the low-dimensional description supply this. *)

(** 两个实际三角形的递增系数相等就足以判等，由低维描述的两条往返律推出。 *)

Lemma cocycle_triangle_eq_of_value@{u p +}
    {M : SetC} `{HM : !Monoid M}
    (x y : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2)
    (H : two_cocycle_triangle_value_resp x ≈S
      two_cocycle_triangle_value_resp y)
  : x ≈S y.
Proof.
  transitivity (two_cocycle_triangle_resp (two_cocycle_triangle_value_resp x)).
  - symmetry. apply two_cocycle_triangle_η.
  - transitivity (two_cocycle_triangle_resp
      (two_cocycle_triangle_value_resp y)).
    + apply func_proper. exact H.
    + apply two_cocycle_triangle_η.
Defined.

(** ** Triangle Operators with Repeated Positions

    Fix respectful labels on triangle operators, with unit labels on both
    degeneracies. Equality of consecutive positions is enough to recognize
    such a degenerate operator, in any target ordinal. *)

(** ** 重复位置的三角形算子

    固定保持三角形算子相等的标签，并假设两种退化均取单位。在任意目标序数中，
    相邻位置相等就足以识别这种退化算子。 *)

Section RepeatedPositions.
Context {M : SetC} `{HM : !Monoid M} {n : nat}
    (t : (@Hom Δ) 2 n → M)
    (t_proper : Proper (HomEq ==> carrier_equiv M) t)
    (t_unit : ∀ (f : (@Hom Δ) 1%nat n) (i : Ordinal 1%nat),
      t (f ∘F σ[1; i]) ≈S 1).

(** A repeated endpoint makes the triangle coefficient a unit. *)

(** 端点重复使三角形系数为单位。 *)

Lemma triangle_label_repeated (f : (@Hom Δ) 2 n)
    (E : (f fin_first = f (fin_first⁺)) ∨
      (f (fin_first⁺) = f (fin_first⁺⁺)))
  : t f ≈S 1.
Proof.
  destruct E as [E | E].
  - pose (Q := ⟦ArrowChain (fmap f
      (ordinal_step (n := 2) (fin_next (fin_first))))⟧Ch).
    transitivity (t (Q ∘F σ[1; fin_first])).
    + apply t_proper. apply (snd (simplex_eq_iff _ _)).
      intros [[] | [[] | [[] | []]]]; first [exact E | reflexivity].
    + apply t_unit.
  - pose (Q := ⟦ArrowChain (fmap f (ordinal_step (n := 2) fin_first))⟧Ch).
    transitivity (t (Q ∘F σ[1; fin_first⁺])).
    + apply t_proper. apply (snd (simplex_eq_iff _ _)).
      intros [[] | [[] | [[] | []]]];
        first [reflexivity | symmetry; exact E].
    + apply t_unit.
Defined.

End RepeatedPositions.

(** ** Reading All Ten Triangle Labels

    Fix normalized respectful labels into a coefficient monoid on all
    triangle operators into [Ord 4]. The canonical ten-entry table recovers
    every operator label, including all repeated-position cases. *)

(** ** 读取全部十个三角形标签

    固定 [Ord 4] 上全部三角形算子的归一化保相等标签，系数为选定幺半群。
    规范十项表恢复每个算子的标签，也包括全部重复位置情形。 *)

Section FourSimplexLabels.
Context {M : SetC} `{HM : !Monoid M}
    (t : (@Hom Δ) 2 4 → M)
    (t_proper : Proper (HomEq ==> carrier_equiv M) t)
    (t_unit : ∀ (f : (@Hom Δ) 1%nat 4) (i : Ordinal 1%nat),
      t (f ∘F σ[1; i]) ≈S 1).

(** The finite table reads exactly the same coefficient as the operator. *)

(** 有限表与算子读取完全相同的系数。 *)

Lemma pentachoron_label_read (f : (@Hom Δ) 2 4)
  : PentachoronLabel
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]))
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺]))
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺]))
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺]))
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first]))
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first]))
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first]))
      (t (δ[3; fin_first⁺] ∘F δ[2; fin_first]))
      (f fin_first) (f (fin_first⁺))
      (f (fin_first⁺⁺)) ≈S t f.
Proof.
  pose proof (ordinal_functor_monotone f fin_first (fin_first⁺)
    (ltac:(cbn; lia))) as Hxy.
  pose proof (ordinal_functor_monotone f (fin_first⁺)
    (fin_first⁺⁺) (ltac:(cbn; lia))) as Hyz.
  remember (f fin_first) as x eqn:Ex.
  remember (f (fin_first⁺)) as y eqn:Ey.
  remember (f (fin_first⁺⁺)) as z eqn:Ez.
  destruct x as [[] | [[] | [[] | [[] | [[] | []]]]]],
    y as [[] | [[] | [[] | [[] | [[] | []]]]]],
    z as [[] | [[] | [[] | [[] | [[] | []]]]]];
    cbn in Hxy, Hyz; try solve [exfalso; lia];
    cbn [PentachoronLabel fin_rank];
    try solve [symmetry; apply (triangle_label_repeated t t_proper t_unit f);
      first [left; congruence | right; congruence]];
    apply t_proper; apply (snd (simplex_eq_iff _ _));
    intros [[] | [[] | [[] | []]]]; cbn;
    first [exact Ex | exact Ey | exact Ez].
Defined.

End FourSimplexLabels.
