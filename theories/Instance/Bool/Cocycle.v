From Cats Require Export
  Cat.Diagram.Cocycle
  Instance.Bool.Group.
From Cats Require Import
  Cat.Shape.Ordinal.

(** * Boolean Coboundaries

    Choose a bit [b(f)] for every arrow, respecting hom equality, and give
    identities the bit [false]. A triangle receives
    [b(f) xor b(g) xor b(g ∘ f)]. This is its coboundary: changing the edge
    labels induces triangle labels satisfying the tetrahedron equation.

    Each of the six edges of a tetrahedron occurs twice, so xor cancels
    it. Associativity identifies the two descriptions of its long edge.
    This construction supplies an instance of the preceding
    %\coqref{Cats.Cat.Diagram.Cocycle.TwoCocycle}{%[TwoCocycle]%}%
    interface and reuses the explicitly selected xor monoid from
    %\coqref{Cats.Instance.Bool.Group.BoolS Monoid}{%[BoolS_Monoid]%}%.
    Importing this module does not register that chosen structure globally.

    A nonzero label in this example is not a proof of a nonzero homotopy
    group: by construction these cocycles are coboundaries. *)

(** * 布尔余边界

    为每条箭头选择一个位 [b(f)]，要求它保持 Hom 相等，并将恒等箭头标为
    [false]。给三角形的标签是 [b(f) xor b(g) xor b(g ∘ f)]。这称为边标签的
    余边界：由它得到的三角形标签满足四面体方程。

    四面体的六条边各出现两次，在异或中相消；结合律识别最长边的两种写法。
    构造实现前面的 %\coqref{Cats.Cat.Diagram.Cocycle.TwoCocycle}{%[TwoCocycle]%}%
    接口，复用 %\coqref{Cats.Instance.Bool.Group.BoolS Monoid}{%[BoolS_Monoid]%}%
    中显式选定的异或幺半群。导入本模块不会全局启用这个选定结构。

    本例的非零标签并不能证明同伦群非零：按构造，这些 cocycle 都是余边界。 *)

(** ** From Edge Labels to Triangle Labels

    Fix a category [J], respectful Boolean labels [b], and their unit law
    [b_id]. The following transparent construction retains the actual bits. *)

(** ** 从边标签得到三角形标签

    固定范畴 [J]、保相等布尔标签 [b] 及其单位律 [b_id]。下列透明构造保留
    实际的布尔位。 *)

Section Coboundary.
Context {J : Cat}
    (b : ∀ {x y : @Ob J}, Hom x y → bool)
    (b_proper : ∀ x y, Proper (HomEq ==> eq) (@b x y))
    (b_id : ∀ x, b (@Cat.Core.id J x) = false).

Arguments b {_ _} _.

Local Existing Instance b_proper.
Local Existing Instance BoolS_Monoid.

(** The xor of the two short-edge bits and the long-edge bit. *)

(** 两条短边与一条长边上布尔位的异或。 *)

Program Definition BoolCoboundary
  : TwoCocycle J BoolS
  :=
  {|two_cocycle_triangle x y z f g := xorb (b f) (xorb (b g) (b (g ∘ f)))
  |}.
Next Obligation.
  intros f f' Hf g g' Hg.
  rewrite (b_proper _ _ _ _ Hf), (b_proper _ _ _ _ Hg).
  rewrite (b_proper _ _ (g ∘ f) (g' ∘ f')).
  - reflexivity.
  - apply comp_proper; assumption.
Defined.
Next Obligation.
  rewrite b_id, (b_proper _ _ _ _ (comp_id_r f)).
  destruct (b f); reflexivity.
Defined.
Next Obligation.
  rewrite b_id, (b_proper _ _ _ _ (comp_id_l f)).
  destruct (b f); reflexivity.
Defined.
Next Obligation.
  rewrite (b_proper _ _ _ _ (comp_assoc h g f)).
  destruct (b f), (b g), (b h), (b (g ∘ f)), (b (h ∘ g)),
    (b (h ∘ (g ∘ f))); reflexivity.
Defined.

(** Evaluating the constructed cocycle computes to its defining xor. *)

(** 构造出的 cocycle 求值后计算为定义中的异或。 *)

Lemma bool_coboundary_triangle {x y z : @Ob J}
    (f : Hom x y) (g : Hom y z)
  : BoolCoboundary⟦f, g⟧₂ = xorb (b f) (xorb (b g) (b (g ∘ f))).
Proof. reflexivity. Defined.

End Coboundary.

(** ** A Triangle with Label One

    In %\coqref{Cats.Cat.Shape.Ordinal.OrdinalShape}{%[OrdinalShape]%}%
    of dimension two, label only the long edge by [true]. Its triangle
    label is [false xor false xor true], hence [true]. In the picture,
    the numbers at the vertices are positions; the numbers on the arrows
    are their Boolean edge labels, written as zero and one. The triangle
    coefficient is their xor, not an extra arrow or a geometric area.
    The long edge is still the composite in the ordinal category; its
    freely chosen edge label need not be the xor of the short-edge labels. *)

(** ** 标签为一的三角形

    在二维 %\coqref{Cats.Cat.Shape.Ordinal.OrdinalShape}{%[OrdinalShape]%}%
    中，只把长边标为 [true]，三角形标签便为 [false xor false xor true]，
    即 [true]。图中顶点的数字表示位置，箭头上的数字则是以零和一书写的
    布尔边标签；三角形系数为这些标签的异或，并非另一条箭头或几何面积。
    长边仍是序数范畴中的复合，但自由选择的边标签不必等于两条短边标签的
    异或。 *)

(** @lang both
%
\[
\begin{tikzcd}[column sep=large,row sep=large]
0 \arrow[r,"{b_{01}=0}"] \arrow[dr,"{b_{02}=1}"'] &
1 \arrow[d,"{b_{12}=0}"] \\
 & 2
\end{tikzcd}
\qquad c_{012}=0+0+1=1 \quad (\bmod\ 2).
\]
% *)

(** The edge bit depends only on its endpoints, so it respects hom equality. *)

(** 边上的布尔位只依赖端点，因此保持 Hom 相等。 *)

Definition bool_triangle_edge {x y : @Ob [Ord 2]} (f : Hom x y)
  : bool
  := andb (Nat.eqb (fin_rank x) 0) (Nat.eqb (fin_rank y) 2).

(** Parallel arrows have the same bit, without inspecting their witnesses. *)

(** 平行箭头具有相同的布尔位，无须检查箭头见证。 *)

Definition bool_triangle_edge_proper (x y : @Ob [Ord 2])
  : Proper (HomEq ==> eq) (@bool_triangle_edge x y).
Proof. intros f g H. reflexivity. Defined.

(** No identity is the long edge from zero to two. *)

(** 恒等箭头不会是从零到二的长边。 *)

Definition bool_triangle_edge_id (x : @Ob [Ord 2])
  : bool_triangle_edge (@Cat.Core.id [Ord 2] x) = false.
Proof. destruct x as [[] | [[] | [[] | []]]]; reflexivity. Defined.

(** Apply the general Boolean coboundary construction to these edge labels. *)

(** 对这些边标签应用一般的布尔余边界构造。 *)

Definition BoolTriangleCocycle
  : @TwoCocycle [Ord 2] BoolS BoolS_Monoid
  := BoolCoboundary (@bool_triangle_edge) bool_triangle_edge_proper
      bool_triangle_edge_id.
