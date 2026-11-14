From Cats Require Export
  Cat.Diagram.Cocycle
  Instance.Set.Simplicial.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Shape.Ordinal
  Cat.Shape.Simplex.Core
  Instance.Set.Lift.

(** * A Simplicial Set of Triangle Labels

    The earlier %\coqref{Cats.Cat.Diagram.Cocycle.TwoCocycle}
    {%[TwoCocycle]%}% gives compatible labels on the triangles of one
    category. Now let that category be [Ord n], and let n vary. An n-simplex
    is one whole cocycle on this ordered shape, not just one coefficient.

    A monotone map [θ : [Ord m] → [Ord n]] selects or repeats positions.
    Pullback reads the old triangle labels at those positions. The existing
    pullback construction already preserves normalization and the
    tetrahedron equation, so faces and degeneracies require no new proofs
    of those laws. The triangle below expresses the resulting simplicial
    composition law: both paths give equal cocycles, coefficient by
    coefficient.

    Coefficients need only form a chosen monoid on a setoid here.
    No Kan fillers or higher homotopy classification are asserted.
    Explicit lifts let the ambient simplex carrier and equality sizes be
    chosen separately, above their respective native bounds. *)

(** * 三角形标签组成的单纯集合

    前面的 %\coqref{Cats.Cat.Diagram.Cocycle.TwoCocycle}
    {%[TwoCocycle]%}% 给出一个范畴上相容的三角形标签。现在令该范畴为
    [Ord n]，再让 n 变化。一个 n-单形是这个有序形状上的一整份 cocycle，
    并非单个系数。

    保序映射 [θ : [Ord m] → [Ord n]] 选择或重复位置，拉回便在这些位置读取
    原有的三角形标签。已有拉回构造保持归一化及四面体方程，因此面与退化
    不需要重新证明这些定律。下图表示所得的单纯复合律：沿两条路径得到的
    cocycle 在每个三角形系数上相等。

    此处系数只须为广集上的选定幺半群，尚未断言 Kan 填充或高阶同伦分类。
    显式提升允许在各自原生上界之上，分别选择单形载体与相等的环境大小。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
Z^2(M)_n \arrow[r,"{\theta^*}"]
  \arrow[dr,"{(\theta\circ\varphi)^*}"'] &
Z^2(M)_m \arrow[d,"{\varphi^*}"] \\
 & Z^2(M)_l
\end{tikzcd}
\end{center}%
*)

(** ** Ordinal Restriction

    Fix a coefficient setoid [M] and its chosen monoid. Ordinal positions
    use native finite equality, whereas their triangle labels use the
    specified equality of [M]. Equal endpoints can therefore be substituted
    without identifying arbitrary equality witnesses. *)

(** ** 序数上的限制

    固定系数广集 [M] 及选定幺半群。序数位置使用有限位置的原生相等，三角形
    标签则使用 [M] 的指定相等。因此可以代换相等端点，而不识别任意相等见证。 *)

Section OrdinalRestriction.
Context {M : SetC} `{HM : !Monoid M}.

(** Equal finite endpoints give equal labels. Parallel ordinal arrows are
    compared by their already specified thin hom equality. *)

(** 相等的有限端点给出相等标签；平行序数箭头用已有的薄 Hom 相等比较。 *)

Lemma ordinal_cocycle_triangle_transport {n : nat}
    (c : TwoCocycle [Ord n] M) {x y z x' y' z' : Ordinal n}
    (Hx : x = x') (Hy : y = y') (Hz : z = z')
    (f : (@Hom [Ord n]) x y) (g : (@Hom [Ord n]) y z)
    (f' : (@Hom [Ord n]) x' y') (g' : (@Hom [Ord n]) y' z')
  : c⟦f, g⟧₂ ≈S c⟦f', g'⟧₂.
Proof.
  destruct Hx, Hy, Hz. apply two_cocycle_triangle_proper; exact tt.
Defined.

(** The native value setoids form a contravariant functor on ordered shapes.
    Respect for operator equality uses finite-position equality, not an
    invariance claim for arbitrary naturally isomorphic functors. *)

(** 原生值广集组成有序形状上的反变函子。保持算子相等使用有限位置相等，
    并未断言对任意自然同构函子的拉回均相等。 *)

Program Definition OrdinalCocycleF
  : Functor (Δ^op) SetCat
  :=
  {|F0 n := @TwoCocycleS [Ord n] M HM
  ; F1 n m θ := two_cocycle_pullback_resp θ
  |}.
Next Obligation.
  intros θ φ H c x y z f g.
  change (c⟦fmap θ f, fmap θ g⟧₂ ≈S c⟦fmap φ f, fmap φ g⟧₂).
  apply ordinal_cocycle_triangle_transport;
    exact (fst (simplex_eq_iff θ φ) H _).
Defined.
Next Obligation. intros c. apply two_cocycle_pullback_id. Defined.
Next Obligation. intros c. apply two_cocycle_pullback_comp. Defined.

End OrdinalRestriction.

(** The actual simplicial set, using the existing lift functor to raise
    native carriers and equality witnesses independently. *)

(** 实际的单纯集合，复用已有提升函子，独立提升原生载体及相等见证。 *)

Definition TwoCocycleSimplicial@{u p +} (M : SetC) `{HM : !Monoid M}
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := LiftF ∘F OrdinalCocycleF (M := M).

Notation "'Z²(' M ')'" := (TwoCocycleSimplicial M) : ob_scope.

(** The unit-labelled cocycle gives a distinguished simplex in every degree. *)

(** 全部标签为单位的 cocycle 给出每一维的一个指定单形。 *)

Definition two_cocycle_simplex_unit@{u p +}
    {M : SetC} `{HM : !Monoid M} (n : nat)
  : (Z²(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n
  :=
  {|lower := UnitTwoCocycle
  |}.

(** Restriction computes by applying the shape operator to both arrows. *)

(** 限制通过将形状算子作用于两条箭头来计算。 *)

Lemma two_cocycle_simplex_restrict@{u p +}
    {M : SetC} `{HM : !Monoid M} {m n : nat}
    (θ : (@Hom Δ) m n)
    (c : (Z²(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
    {x y z : Ordinal m}
    (f : (@Hom [Ord m]) x y) (g : (@Hom [Ord m]) y z)
  : (lower (Z²(M)[θ]Δ c))⟦f, g⟧₂ ≈S
      (lower c)⟦fmap θ f, fmap θ g⟧₂.
Proof. reflexivity. Defined.

(** Every restriction preserves the distinguished unit simplex. *)

(** 每个限制都保持指定的单位单形。 *)

Lemma two_cocycle_simplex_unit_restrict@{u p +}
    {M : SetC} `{HM : !Monoid M} {m n : nat}
    (θ : (@Hom Δ) m n)
  : Z²(M)[θ]Δ (two_cocycle_simplex_unit n) ≈S
      (two_cocycle_simplex_unit m :
        (Z²(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) m).
Proof.
  refine {|lower := _
          |}. apply two_cocycle_pullback_unit.
Defined.
