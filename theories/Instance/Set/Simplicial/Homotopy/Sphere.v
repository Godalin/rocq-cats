From Cats Require Export
  Instance.Set.Simplicial.Operators.
From Cats.Set Require Export
  Subset
  Generated.
From Cats Require Import
  Cat.Diagram.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Based Two-Spheres and Their Elementary Homotopies

    A based two-sphere is a triangle whose three edges are the constant
    edge at a specified vertex. The triangle is retained as data; its
    boundary equations do not identify it with the constant triangle.
    Think of its boundary as collapsed to the basepoint; this is a
    combinatorial description, without constructing a geometric realization.

    An elementary homotopy is an actual tetrahedron: faces zero and one
    are constant, and faces two and three are the two spheres. This is the
    usual simplex presentation of a based sphere homotopy. We then generate
    an equivalence relation, including the original specified equality.
    No Kan hypothesis is needed to form these data. In particular, we do
    not assume that elementary homotopies are already an equivalence, or
    that the resulting setoid already carries a homotopy-group operation.
    In the diagram, [b_k] denotes the constant k-simplex at the base vertex. *)

(** * 基点二维球面及其初等同伦

    基点二维球面是三条边均为指定顶点处常值边的三角形。三角形本身仍为数据；
    边界方程不会将它识别为常值三角形。
    可以将其理解为把边界压到基点；这只是组合描述，没有构造几何实现。

    初等同伦是一份实际四面体：第零、第一面为常值，第二、第三面为两个球面。
    这是基点球面同伦的通常单形呈现。随后加入原有指定相等并生成等价关系。
    形成这些数据不要求 Kan 假设；尤其不预设初等同伦已为等价关系，也不预设
    所得广集已具备同伦群运算。图中 [b_k] 表示基点处的常值 k-单形。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
& w\in X_3 \arrow[dl,"d_2"'] \arrow[dr,"d_3"] & \\
x\in X_2 && y\in X_2
\end{tikzcd}
\qquad $d_0w=d_1w=b_2,\quad d_ix=d_iy=b_1.$
\end{center}%
*)

(** ** Constant Simplices at One Vertex

    Fix a simplicial setoid with independent value sizes and a vertex.
    Restriction along the constant ordinal operator supplies its constant
    simplex in every degree, without selecting terminal or product data. *)

(** ** 一个顶点处的常值单形

    固定值大小独立的单纯广集及一个顶点。沿常值序数算子的限制给出每一维
    常值单形，无须选定终对象或积结构。 *)

Section ConstantSimplices.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Collapse every position to the specified vertex. *)

(** 将所有位置压到指定顶点。 *)

Definition simplex_constant (n : nat)
  : X n
  := X[ConstF [Ord n] (C := [Ord 0]) fin_first]Δ b.

(** Every restriction of a constant simplex is constant. *)

(** 常值单形的每个限制仍为常值。 *)

Lemma simplex_constant_restrict {m n : nat} (θ : (@Hom Δ) m n)
  : X[θ]Δ (simplex_constant n) ≈S simplex_constant m.
Proof.
  unfold simplex_constant.
  transitivity (X[@comp Δ m n 0
    (ConstF [Ord n] (C := [Ord 0]) fin_first) θ]Δ b).
  - symmetry. apply simplex_restrict_comp.
  - apply simplex_restrict_proper.
    apply (snd (simplex_eq_iff _ _)). intros i. reflexivity.
Defined.

End ConstantSimplices.

(** A simplicial map sends constant simplices to constants at the image
    vertex, by naturality rather than native equality. *)

(** 由自然性，单纯映射将常值单形送到像顶点处的常值单形，而非要求原生相等。 *)

Lemma simplex_constant_natural@{u p +}
    {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (α : X ⇒ Y) (b : X 0) (n : nat)
  : α n (simplex_constant X b n) ≈S
      simplex_constant Y (α 0 b) n.
Proof. apply simplex_restrict_natural. Defined.

(** ** Spheres and Generated Homotopy Classes

    Fix the simplicial setoid and base vertex. Subsets retain all boundary
    witnesses, whereas equality compares only the underlying triangle.
    The generated relation also retains tetrahedra and finite derivations;
    its witness universe must therefore contain those data. *)

(** ** 球面与生成同伦类

    固定单纯广集及基点顶点。子集保留全部边界见证，相等只比较底层三角形。
    生成关系还保留四面体及有限推导，其见证宇宙因此须容纳这些数据。 *)

Section TwoSpheres.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** A triangle with all edges fixed at the base vertex. *)

(** 全部边均固定于基点顶点的三角形。 *)

Definition TwoSphereS
  : SetC
  := SubsetS (X 2)
      (λ x, ∀ i : Ordinal 2, d[X; 1; i] x ≈S simplex_constant X b 1).

(** The constant triangle is the distinguished sphere. *)

(** 常值三角形为指定球面。 *)

Definition two_sphere_base
  : TwoSphereS
  := (simplex_constant X b 2; λ i, simplex_constant_restrict X b δ[1; i]).

(** Actual three-dimensional data with the specified four faces. Endpoints
    are compared in specified equality; boundary witnesses are not compared. *)

(** 带指定四个面的实际三维数据。端点按指定相等比较，不比较边界见证。 *)

Definition TwoSphereHomotopy (x y : TwoSphereS)
  : Type
  := ∃ w : X 3,
      (d[X; 2; fin_first] w ≈S simplex_constant X b 2) ∧
      (d[X; 2; fin_first⁺] w ≈S simplex_constant X b 2) ∧
      (d[X; 2; fin_first⁺⁺] w ≈S x.1) ∧
      (d[X; 2; fin_first⁺⁺⁺] w ≈S y.1).

(** Change endpoint representatives while retaining the very same
    tetrahedron and its constant faces. *)

(** 更换端点代表，保留完全相同的四面体及其常值面。 *)

Definition TwoSphereHomotopyChangeEndpoints
    {x y x' y' : TwoSphereS} (H : TwoSphereHomotopy x y)
    (E : x ≈S x') (F : y ≈S y')
  : TwoSphereHomotopy x' y'.
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]].
  exists w. split; [exact H0 |]. split; [exact H1 |]. split.
  - transitivity x.1; assumption.
  - transitivity y.1; assumption.
Defined.

(** Elementary homotopy respects specified equality at both endpoints,
    with two transparent witness transformations. *)

(** 初等同伦保持两个端点的指定相等，提供两个透明的见证转换。 *)

Global Instance TwoSphereHomotopy_proper
  : Proper ([≈S] ==> [≈S] ==> iffT) TwoSphereHomotopy.
Proof.
  intros x x' E y y' F. split; intros H.
  - exact (TwoSphereHomotopyChangeEndpoints H E F).
  - exact (TwoSphereHomotopyChangeEndpoints H (symmetry E) (symmetry F)).
Defined.

(** Retain both equality changes of representative and elementary
    homotopies as generators. No quotient of native elements is taken. *)

(** 将代表的相等替换与初等同伦均保留为生成元，不对原生元素取商。 *)

Definition TwoSphereClassS
  : SetC
  := GeneratedS TwoSphereS (λ x y, ((x ≈S y) + TwoSphereHomotopy x y)%type).

(** Specified equality gives the corresponding class equality. *)

(** 指定相等给出相应的类相等。 *)

Definition two_sphere_class_eq {x y : TwoSphereS} (H : x ≈S y)
  : (x : TwoSphereClassS) ≈S y
  := closure_step (inl H).

(** An actual tetrahedron gives a class equality in the forward direction. *)

(** 实际四面体给出正向的类相等。 *)

Definition two_sphere_class_step {x y : TwoSphereS}
    (H : TwoSphereHomotopy x y)
  : (x : TwoSphereClassS) ≈S y
  := closure_step (inr H).

(** The class projection retains the same representative triangle and
    changes only its equality policy. *)

(** 类投影保留同一个代表三角形，只改变其相等规则。 *)

Program Definition two_sphere_class_resp
  : TwoSphereS →r TwoSphereClassS
  :=
  {|func x := x
  |}.
Next Obligation. intros x y H. exact (two_sphere_class_eq H). Defined.

(** Any respectful invariant of elementary homotopies descends to the
    generated class setoid, using the existing generated-setoid theorem. *)

(** 初等同伦的任意保相等不变量，都由已有生成广集定理下降到生成类广集。 *)

Definition two_sphere_class_desc {A : SetC} (f : TwoSphereS →r A)
    (H : ∀ x y, TwoSphereHomotopy x y → f x ≈S f y)
  : TwoSphereClassS →r A.
Proof.
  refine (generated_resp f _). intros x y [E | E].
  - exact (@func_proper _ _ f x y E).
  - exact (H x y E).
Defined.

End TwoSpheres.

(** ** Mapping Spheres

    Fix a simplicial map between independently sized values at common
    ambient bounds. Naturality transports all boundary and tetrahedron
    equations to the image base vertex. *)

(** ** 映射球面

    固定共同环境界内的单纯映射。自然性将所有边界及四面体方程运输到像基点
    顶点处。 *)

Section MappingSpheres.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (α : X ⇒ Y) (b : X 0).

(** Apply a simplicial map to the retained triangle. *)

(** 对保留的三角形施加单纯映射。 *)

Program Definition two_sphere_map_resp
  : TwoSphereS X b →r TwoSphereS Y (α 0 b)
  :=
  {|func x := (α 2 x.1; _)
  |}.
Next Obligation.
  intros i.
  transitivity (α 1 (d[X; 1; i] x.1)).
  - symmetry. apply simplex_face_natural.
  - transitivity (α 1 (simplex_constant X b 1)).
    + apply func_proper. exact (x.2 i).
    + apply simplex_constant_natural.
Defined.
Next Obligation. intros x y H. exact (@func_proper _ _ (α 2) _ _ H). Defined.

(** The image of an elementary homotopy is its image tetrahedron. *)

(** 初等同伦的像就是其四面体的像。 *)

Definition two_sphere_homotopy_map {x y : TwoSphereS X b}
    (H : TwoSphereHomotopy X b x y)
  : TwoSphereHomotopy Y (α 0 b)
      (two_sphere_map_resp x) (two_sphere_map_resp y).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]]. exists (α 3 w).
  assert (E : ∀ i : Ordinal 3,
      d[Y; 2; i] (α 3 w) ≈S α 2 (d[X; 2; i] w)).
  { intros i. symmetry. apply simplex_face_natural. }
  split; [| split; [| split]].
  - transitivity (α 2 (d[X; 2; fin_first] w)); [apply E |].
    etransitivity; [apply func_proper; exact H0 |].
    apply simplex_constant_natural.
  - transitivity (α 2 (d[X; 2; fin_first⁺] w)); [apply E |].
    etransitivity; [apply func_proper; exact H1 |].
    apply simplex_constant_natural.
  - transitivity (α 2 (d[X; 2; fin_first⁺⁺] w)); [apply E |].
    apply func_proper. exact H2.
  - transitivity (α 2 (d[X; 2; fin_first⁺⁺⁺] w)); [apply E |].
    apply func_proper. exact H3.
Defined.

End MappingSpheres.
