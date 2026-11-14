From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Core
  Instance.Set.Simplicial.Operators.

Local Open Scope monoid_scope.

(** * Points, Edges and Freely Labelled Triangles

    The shape [Ord 0] has only identity arrows. In [Ord 1], a pair of
    consecutive arrows must contain an identity. Normalization therefore
    makes all triangle labels units in these two degrees. In [Ord 2] there
    is exactly one strictly increasing triangle, with vertices [012]; its
    coefficient is free.

    The diagram distinguishes the positions from the data of the model.
    Its three sides all represent the unique edge, but the triangle itself
    has coefficient a. Repeating a position forces the unit coefficient.
    The laws below make this description precise in specified equality,
    without identifying cocycle records or their proofs. *)

(** * 点、边与可自由标记的三角形

    形状 [Ord 0] 只有恒等箭头。在 [Ord 1] 中，一对相邻箭头必有一条恒等，
    因此归一化使这两维中的三角形标签全为单位。[Ord 2] 中恰有一个严格递增
    的三角形，顶点为 [012]，其系数可以自由选择。

    下图区分了位置与模型中的数据：三条边都表示唯一的边，整个三角形却带有
    系数 a。重复一个位置会迫使系数为单位。下列定律在指定相等中明确表达
    这一描述，不识别 cocycle 记录或其定律证明。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& 1 \arrow[dr,"e"] & \\
0 \arrow[ur,"e"] \arrow[rr,"e"'] && 2
\end{tikzcd}
\qquad $c_{012}=a,\qquad c_{iik}=c_{ikk}=1.$
\end{center}%
*)

(** ** The Native Low-Dimensional Cocycles

    Fix a coefficient setoid [M] with its selected monoid. All finite
    case analysis concerns concrete ordinal positions and order witnesses;
    coefficients retain their own specified equality. *)

(** ** 原生低维 cocycle

    固定系数广集 [M] 及选定幺半群。有限分类只检查具体序数位置与顺序见证；
    系数保留自身的指定相等。 *)

Section NativeLow.
Context {M : SetC} `{HM : !Monoid M}.

(** Every zero-dimensional cocycle is equal to the unit-labelled one. *)

(** 每个零维 cocycle 都与单位标签的 cocycle 相等。 *)

Lemma ordinal_cocycle_zero_unit (c : TwoCocycle [Ord 0] M)
  : TwoCocycleEq c UnitTwoCocycle.
Proof.
  intros [[] | []] [[] | []] [[] | []] f g.
  cbn in f, g. destruct f, g. apply two_cocycle_unit_l.
Defined.

(** Every triangle on two ordered positions repeats a consecutive position. *)

(** 两个有序位置上的三角形必重复一个相邻位置。 *)

Lemma ordinal_cocycle_one_unit (c : TwoCocycle [Ord 1] M)
  : TwoCocycleEq c UnitTwoCocycle.
Proof.
  intros x y z f g.
  destruct x as [[] | [[] | []]], y as [[] | [[] | []]],
    z as [[] | [[] | []]]; cbn in f, g; destruct f, g;
    first [apply two_cocycle_unit_l | apply two_cocycle_unit_r].
Defined.

(** Give the strictly increasing triangle its chosen coefficient; every
    repeated-position triangle receives the unit. *)

(** 给严格递增三角形选定的系数；重复位置的三角形均取单位。 *)

Definition ordinal_triangle_label (a : M) (x y z : Ordinal 2)
  : M
  := match x, y, z with
     | inl _, inr (inl _), inr (inr (inl _)) => a
     | _, _, _ => 1
     end.

(** The free label extends to a whole normalized cocycle on [Ord 2].
    Its tetrahedra repeat positions, so the unit laws suffice. *)

(** 自由标签延伸为 [Ord 2] 上完整的归一化 cocycle；其四面体必重复位置，
    因而单位律已经足够。 *)

Program Definition TriangleTwoCocycle (a : M)
  : TwoCocycle [Ord 2] M
  :=
  {|two_cocycle_triangle x y z f g := ordinal_triangle_label a x y z
  |}.
Next Obligation. intros f f' Hf g g' Hg. reflexivity. Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | []]]], y as [[] | [[] | [[] | []]]];
    reflexivity.
Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | []]]], y as [[] | [[] | [[] | []]]];
    reflexivity.
Defined.
Next Obligation.
  destruct x as [[] | [[] | [[] | []]]], y as [[] | [[] | [[] | []]]],
    z as [[] | [[] | [[] | []]]], w as [[] | [[] | [[] | []]]];
    cbn in *; try solve [destruct f | destruct g | destruct h];
    rewrite ?monoid_unit_l, ?monoid_unit_r; reflexivity.
Defined.

(** Read the single strictly increasing triangle coefficient. *)

(** 读取唯一严格递增三角形的系数。 *)

Definition ordinal_cocycle_triangle_value (c : TwoCocycle [Ord 2] M)
  : M
  := c⟦ordinal_step (@fin_first 1),
      ordinal_step (fin_next (@fin_first 0))⟧₂.

(** Reading a freely labelled triangle recovers the original coefficient. *)

(** 读取自由标记的三角形，恢复原系数。 *)

Lemma triangle_two_cocycle_β (a : M)
  : ordinal_cocycle_triangle_value (TriangleTwoCocycle a) ≈S a.
Proof. reflexivity. Defined.

(** The coefficient determines the whole cocycle in degree two. *)

(** 二维中的这一系数确定整个 cocycle。 *)

Lemma triangle_two_cocycle_η (c : TwoCocycle [Ord 2] M)
  : TwoCocycleEq
      (TriangleTwoCocycle (ordinal_cocycle_triangle_value c)) c.
Proof.
  intros x y z f g.
  destruct x as [[] | [[] | [[] | []]]], y as [[] | [[] | [[] | []]]],
    z as [[] | [[] | [[] | []]]]; cbn in f, g; destruct f, g;
    try reflexivity; symmetry;
    first [apply two_cocycle_unit_l | apply two_cocycle_unit_r].
Defined.

End NativeLow.

(** ** Low Degrees of the Actual Simplicial Set

    Choose ambient value sizes [u], [p] independently above the native
    bounds. Wrappers retain the original cocycle and its equality witnesses. *)

(** ** 实际单纯集合的低维

    在原生上界之上独立选择环境值大小 [u]、[p]；包装保留原 cocycle 及其
    相等见证。 *)

Section SimplicialLow.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}.

(** All vertices are equal. *)

(** 所有顶点相等。 *)

Lemma two_cocycle_zero_unique
    (x y : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 0)
  : x ≈S y.
Proof.
  refine {|lower := _
          |}.
  transitivity (@UnitTwoCocycle [Ord 0] M HM);
    [apply ordinal_cocycle_zero_unit | symmetry; apply ordinal_cocycle_zero_unit].
Defined.

(** All edges are equal; this does not force all triangles to agree. *)

(** 所有边相等，但这并不迫使所有三角形相等。 *)

Lemma two_cocycle_one_unique
    (x y : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 1%nat)
  : x ≈S y.
Proof.
  refine {|lower := _
          |}.
  transitivity (@UnitTwoCocycle [Ord 1] M HM);
    [apply ordinal_cocycle_one_unit | symmetry; apply ordinal_cocycle_one_unit].
Defined.

(** The coefficient gives an actual two-simplex, preserving coefficient
    equality without comparing construction proofs. *)

(** 系数给出实际的二维单形，保持系数相等而不比较构造证明。 *)

Program Definition two_cocycle_triangle_resp
  : M →r (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2
  :=
  {|func a :=
      {|lower := TriangleTwoCocycle a
      |}
  |}.
Next Obligation.
  intros a b H. refine {|lower := _
                       |}.
  intros x y z f g.
  destruct x as [[] | [[] | [[] | []]]], y as [[] | [[] | [[] | []]]],
    z as [[] | [[] | [[] | []]]]; cbn; try reflexivity; exact H.
Defined.

(** Evaluate a two-simplex at its increasing triangle. *)

(** 在严格递增的三角形处对二维单形求值。 *)

Program Definition two_cocycle_triangle_value_resp
  : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2 →r M
  :=
  {|func c := ordinal_cocycle_triangle_value (lower c)
  |}.
Next Obligation. intros c d [H]. apply H. Defined.

(** Construction followed by evaluation recovers the coefficient. *)

(** 先构造再求值，恢复系数。 *)

Lemma two_cocycle_triangle_β (a : M)
  : two_cocycle_triangle_value_resp (two_cocycle_triangle_resp a) ≈S a.
Proof. apply triangle_two_cocycle_β. Defined.

(** Evaluation followed by construction recovers the whole two-simplex. *)

(** 先求值再构造，恢复整个二维单形。 *)

Lemma two_cocycle_triangle_η
    (c : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2)
  : two_cocycle_triangle_resp (two_cocycle_triangle_value_resp c) ≈S c.
Proof.
  refine {|lower := _
          |}. apply triangle_two_cocycle_η.
Defined.

(** Every triangle obtained by degenerating an edge has the unit label. *)

(** 由边退化而来的每个三角形都具有单位标签。 *)

Lemma two_cocycle_degenerate_one
    (c : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 1%nat)
    (i : Fin@{Set} 2)
  : s[Z²(M); 1%nat; i] c ≈S two_cocycle_simplex_unit 2.
Proof.
  transitivity (s[Z²(M); 1%nat; i] (two_cocycle_simplex_unit 1%nat)).
  - apply func_proper. apply two_cocycle_one_unique.
  - apply two_cocycle_simplex_unit_restrict.
Defined.

End SimplicialLow.
