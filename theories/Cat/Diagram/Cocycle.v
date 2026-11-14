From Cats Require Export
  Algebra.Monoid.Core
  Cat.Core
  Cat.Functor.Core.

Local Open Scope monoid_scope.

(** * Normalized Triangle Data

    A composable pair [f : x → y], [g : y → z] determines a triangle:
    its long edge is [g ∘ f]. A two-cocycle assigns a coefficient [c(f,g)]
    to that triangle. If either short edge [f] or [g] is an identity, the
    coefficient must be [1]; this is the meaning of normalized. An identity
    long edge alone does not impose this condition.

    Number [x,y,z,w] as [0,1,2,3]. Four vertices give four triangles.
    The tetrahedron equation compares
    the products of coefficients on its two pairs of faces. In additive
    notation it reads [c012 + c023 = c123 + c013]. It constrains triangle
    labels, rather than asking for a new arrow between the vertices.
    The arrows in the picture commute by the category composition laws;
    the extra equation on their labels is [two_cocycle_tetrahedron] below.

    The present interface only needs a monoid on a set with specified
    equality. It constructs neither a simplicial object nor Kan fillers.
    The familiar higher simplicial examples will require additional
    hypotheses on the coefficients, in particular abelian group structure. *)

(** * 归一化三角形数据

    可复合的 [f : x → y]、[g : y → z] 给出一个三角形，长边为 [g ∘ f]。
    二维 cocycle 为它赋一个系数 [c(f,g)]。若短边 [f] 或 [g] 为恒等，系数就
    必须为 [1]；这就是“归一化”的含义。只有长边为恒等并不施加此条件。

    将 [x,y,z,w] 依次编号为 [0,1,2,3]，四个顶点给出四个三角形。
    四面体方程比较两对面上系数的乘积；改用加法
    记号就是 [c012 + c023 = c123 + c013]。它约束三角形的标签，并不要求
    在顶点间另造一条箭头。图中的箭头由范畴复合律交换；标签额外满足的
    方程则是下方的 [two_cocycle_tetrahedron]。

    当前接口只要求带指定相等的广集上有幺半群结构，尚未构造单纯对象或
    Kan 填充。通常的高阶单纯例子还需要系数的额外条件，尤其是交换群结构。 *)

(** @lang both
%
\[
\begin{gathered}
\begin{tikzcd}[column sep=large]
 x \arrow[r,"f"'] \arrow[rr,bend left=35,"g\circ f"]
   \arrow[rrr,bend left=65,"h\circ g\circ f"] &
 y \arrow[r,"g"'] \arrow[rr,bend right=35,"h\circ g"'] &
 z \arrow[r,"h"'] & w
\end{tikzcd}
\\[1em]
c_{012}c_{023}=c_{123}c_{013}.
\end{gathered}
\]
% *)

Record TwoCocycle (J : Cat) (M : SetC) `{HM : !Monoid M}
  :=
  { two_cocycle_triangle :> ∀ {x y z : @Ob J},
      Hom x y → Hom y z → M
  ; two_cocycle_triangle_proper {x y z}
    :: Proper (HomEq ==> HomEq ==> carrier_equiv M)
        (@two_cocycle_triangle x y z)
  ; two_cocycle_unit_l {x y} (f : Hom x y)
    : two_cocycle_triangle id f ≈S 1
  ; two_cocycle_unit_r {x y} (f : Hom x y)
    : two_cocycle_triangle f id ≈S 1
  ; two_cocycle_tetrahedron {x y z w}
      (f : Hom x y) (g : Hom y z) (h : Hom z w)
    : two_cocycle_triangle f g ⋅ two_cocycle_triangle (g ∘ f) h ≈S
        two_cocycle_triangle g h ⋅ two_cocycle_triangle f (h ∘ g)
  }.

Arguments two_cocycle_triangle {_ _ _} _ {_ _ _} _ _.

(** Apply the underlying label function to a composable pair. Endpoints
    are inferred from the two arrows. *)

(** 将底层标签函数作用于可复合的一对箭头；端点由两条箭头推断。 *)

Notation "c '⟦' f ',' g '⟧₂'" := (c _ _ _ f g)
  (at level 1, format "c ⟦ f ,  g ⟧₂") : cat_scope.

(** ** Equality and Constant Labels

    Fix a category [J] and a chosen coefficient monoid [M]. Compare cocycles
    on each triangle in the specified equality of [M]. Their preservation
    and law witnesses remain data; equality does not compare those fields. *)

(** ** 相等与常值标签

    固定范畴 [J] 及系数广集 [M] 上选定的幺半群。逐个三角形用 [M] 的指定
    相等比较 cocycle。保相等及定律见证仍是数据，相等不比较这些字段。 *)

Section Equality.
Context {J : Cat} {M : SetC} `{HM : !Monoid M}.

(** Pointwise equality of triangle labels, valued in [Type]. *)

(** 三角形标签的逐点相等，取值于 [Type]。 *)

Definition TwoCocycleEq (c d : TwoCocycle J M)
  : Type
  := ∀ x y z : @Ob J, ∀ (f : Hom x y) (g : Hom y z),
      c⟦f, g⟧₂ ≈S d⟦f, g⟧₂.

(** The equivalence laws are inherited pointwise from [M]. *)

(** 等价律逐点继承自 [M]。 *)

Program Instance TwoCocycleEq_Equivalence
  : Equivalence TwoCocycleEq.
Next Obligation. intros c x y z f g. reflexivity. Defined.
Next Obligation. intros c d H x y z f g. symmetry. apply H. Defined.
Next Obligation.
  intros c d e H K x y z f g.
  transitivity (d⟦f, g⟧₂); [apply H | apply K].
Defined.

(** The set of cocycles uses this equality, without function extensionality. *)

(** cocycle 广集采用此相等，不需要函数外延性。 *)

Program Canonical TwoCocycleS
  : SetC
  :=
  {|carrier := TwoCocycle J M
  ; carrier_equiv := TwoCocycleEq
  ; carrier_setoid := TwoCocycleEq_Equivalence
  |}.

(** Label every triangle by the unit. This selected cocycle is transparent. *)

(** 将每个三角形标为单位；此选定 cocycle 保持透明。 *)

Program Definition UnitTwoCocycle
  : TwoCocycle J M
  :=
  {|two_cocycle_triangle x y z f g := 1
  |}.
Next Obligation. intros f f' Hf g g' Hg. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

End Equality.

(** ** Pullback along a Functor

    A functor [F : I → J] sends each triangle in [I] to one in [J].
    Read its old label there. The image of a composite agrees with the
    composite of the images by
    %\coqref{Cats.Cat.Functor.Core.functor comp}{%[functor_comp]%}%.
    Respectfulness of the labels converts that hom equality into coefficient
    equality. This is why the tetrahedron equation survives pullback.

    No inverse map, natural isomorphism or equality of object maps is used.
    Identity and composition are compared pointwise in the cocycle set. *)

(** ** 沿函子拉回

    函子 [F : I → J] 将 [I] 的每个三角形送到 [J]，读取其原有标签即可。
    复合的像与像的复合由
    %\coqref{Cats.Cat.Functor.Core.functor comp}{%[functor_comp]%}%
    相等；标签的保相等性再将此 Hom 相等转成系数相等。因此四面体方程在
    拉回后仍成立。

    这里不使用逆映射、自然同构或对象映射的相等；恒等与复合律都在 cocycle
    广集中逐点比较。 *)

Section Pullback.
Context {I J : Cat} {M : SetC} `{HM : !Monoid M}.

(** Precompose the two arrow inputs with the functor's arrow map. *)

(** 在两个箭头输入处预复合函子的箭头映射。 *)

Program Definition TwoCocyclePullback (F : Functor I J)
    (c : TwoCocycle J M)
  : TwoCocycle I M
  :=
  {|two_cocycle_triangle x y z f g := c⟦fmap F f, fmap F g⟧₂
  |}.
Next Obligation.
  intros f f' Hf g g' Hg. apply two_cocycle_triangle_proper;
    apply functor_fmap_proper; assumption.
Defined.
Next Obligation.
  rewrite functor_id. apply two_cocycle_unit_l.
Defined.
Next Obligation.
  rewrite functor_id. apply two_cocycle_unit_r.
Defined.
Next Obligation.
  transitivity (c⟦fmap F f, fmap F g⟧₂ ⋅
    c⟦fmap F g ∘ fmap F f, fmap F h⟧₂).
  - apply magma_mul_proper; [reflexivity |].
    apply two_cocycle_triangle_proper; [apply functor_comp | reflexivity].
  - transitivity (c⟦fmap F g, fmap F h⟧₂ ⋅
      c⟦fmap F f, fmap F h ∘ fmap F g⟧₂).
    + apply two_cocycle_tetrahedron.
    + apply magma_mul_proper; [reflexivity |].
      apply two_cocycle_triangle_proper;
        [reflexivity | symmetry; apply functor_comp].
Defined.

(** Pullback preserves equality of cocycles, retaining its witness. *)

(** 拉回保持 cocycle 的相等，并保留相等见证。 *)

Program Definition two_cocycle_pullback_resp (F : Functor I J)
  : @TwoCocycleS J M HM →r @TwoCocycleS I M HM
  :=
  {|func c := TwoCocyclePullback F c
  |}.
Next Obligation. intros c d H x y z f g. apply H. Defined.

(** Pulling back constant labels still gives constant labels. *)

(** 常值标签拉回后仍为常值标签。 *)

Lemma two_cocycle_pullback_unit (F : Functor I J)
  : TwoCocycleEq (TwoCocyclePullback F UnitTwoCocycle) UnitTwoCocycle.
Proof. intros x y z f g. reflexivity. Defined.

End Pullback.

(** Pullback along an identity functor leaves every triangle label equal. *)

(** 沿恒等函子拉回后，每个三角形的标签相等。 *)

Lemma two_cocycle_pullback_id {J : Cat} {M : SetC} `{HM : !Monoid M}
    (c : TwoCocycle J M)
  : TwoCocycleEq (TwoCocyclePullback IdF c) c.
Proof. intros x y z f g. reflexivity. Defined.

(** Pull back along the composite, or first along [G] and then along [F].
    Only the labels are compared, not the stored functor-law witnesses. *)

(** 沿复合拉回，等于先沿 [G] 再沿 [F] 拉回；只比较标签，不比较保存的函子律
    见证。 *)

Lemma two_cocycle_pullback_comp {I J K : Cat} {M : SetC}
    `{HM : !Monoid M} (F : Functor I J) (G : Functor J K)
    (c : TwoCocycle K M)
  : TwoCocycleEq (TwoCocyclePullback (G ∘F F) c)
      (TwoCocyclePullback F (TwoCocyclePullback G c)).
Proof. intros x y z f g. reflexivity. Defined.
