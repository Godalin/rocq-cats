From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereComposition.
From Cats Require Import
  Cat.Core
  Cat.Natural
  Instance.Set.Isomorphism.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Mapping Sphere Classes and Transporting Equal Base Vertices

    A simplicial map sends a based triangle to a based triangle and an
    elementary homotopy to its image tetrahedron. The descent theorem from
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.Sphere.two sphere class desc}
    {%[two_sphere_class_desc]%}% therefore gives a map on generated classes.
    No Kan structure or group operation is needed for this first step.

    Image base vertices need not be definitionally identical. We first
    transport along their specified setoid equality, keeping the triangle
    itself and changing only its boundary witnesses. The laws below compare
    classes, not those witnesses. This is equality transport; an arbitrary
    edge between vertices is different data and is not handled here.
    After constructing class group operations, return to these same maps
    through
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_map_mul}
    {%[two_sphere_class_map_mul]%}%: the actual image tetrahedron below
    supplies product preservation even for independent filler choices. *)

(** * 映射球面类及运输相等的基点顶点

    单纯映射将基点三角形送到基点三角形，将初等同伦送到其像四面体。因此，
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.Sphere.two sphere class desc}
    {%[two_sphere_class_desc]%}% 的下降定理给出生成类上的映射。
    这第一步不要求 Kan 结构或群运算。

    像基点顶点不必定义相同。先沿其指定广集相等运输，保持三角形本身，仅更换
    边界见证。下方定律比较类，不比较这些见证。这是相等运输；顶点之间的任意
    边是另一种数据，此处尚不处理。构造类群运算后，可通过
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_map_mul}
    {%[two_sphere_class_map_mul]%}% 返回这些相同映射：下方的实际像四面体
    给出乘积保持，即使填充选择相互独立。 *)

(** ** Transport along Specified Vertex Equality

    Fix independent ambient sizes and a simplicial setoid. Vertex equality
    is acted on by restriction maps; no elimination of native equality or
    identification of Type-valued equality witnesses is used. *)

(** ** 沿指定顶点相等运输

    固定独立环境大小及单纯广集。限制映射作用于顶点相等；不消去原生相等，
    也不识别 Type 值相等见证。 *)

Section SphereBaseEquality.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

(** Constants respect the specified equality of their vertices. *)

(** 常值单形保持其顶点的指定相等。 *)

Lemma simplex_constant_vertex_eq {b c : X 0} (E : b ≈S c) (n : nat)
  : simplex_constant X b n ≈S simplex_constant X c n.
Proof. apply func_proper. exact E. Defined.

(** Keep the triangle and replace its three constant-boundary witnesses. *)

(** 保持三角形，更换其三份常值边界见证。 *)

Program Definition two_sphere_change_base_resp {b c : X 0} (E : b ≈S c)
  : TwoSphereS X b →r TwoSphereS X c
  :=
  {|func x := (x.1; _)
  |}.
Next Obligation.
  intros i. transitivity (simplex_constant X b 1).
  - exact (x.2 i).
  - apply simplex_constant_vertex_eq. exact E.
Defined.
Next Obligation. intros x y H. exact H. Defined.

(** The same tetrahedron witnesses the transported elementary homotopy. *)

(** 同一四面体见证运输后的初等同伦。 *)

Definition two_sphere_homotopy_change_base {b c : X 0} (E : b ≈S c)
    {x y : TwoSphereS X b} (H : TwoSphereHomotopy X b x y)
  : TwoSphereHomotopy X c
      (two_sphere_change_base_resp E x) (two_sphere_change_base_resp E y).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]]. exists w.
  split; [| split; [| split]].
  - transitivity (simplex_constant X b 2); [exact H0 |].
    apply simplex_constant_vertex_eq. exact E.
  - transitivity (simplex_constant X b 2); [exact H1 |].
    apply simplex_constant_vertex_eq. exact E.
  - exact H2.
  - exact H3.
Defined.

(** Descent retains arbitrary finite class derivations at the new base. *)

(** 下降在新基点处保留任意有限类推导。 *)

Definition two_sphere_class_change_base_resp {b c : X 0} (E : b ≈S c)
  : TwoSphereClassS X b →r TwoSphereClassS X c.
Proof.
  refine (two_sphere_class_desc X b
    (two_sphere_class_resp X c ∘r two_sphere_change_base_resp E) _).
  intros x y H. apply two_sphere_class_step.
  exact (two_sphere_homotopy_change_base E H).
Defined.

(** Reflexive transport is the identity in class equality. *)

(** 自反运输在类相等中为恒等。 *)

Lemma two_sphere_class_change_base_id (b : X 0) (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp (reflexivity b) x ≈S x.
Proof.
  apply (two_sphere_class_eq X b).
  change (x.1 ≈S x.1). reflexivity.
Defined.

(** Successive transports agree with transport along the composed equality. *)

(** 依次运输与沿复合相等的运输一致。 *)

Lemma two_sphere_class_change_base_comp {b c d : X 0}
    (E : b ≈S c) (F : c ≈S d) (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp F
      (two_sphere_class_change_base_resp E x) ≈S
      two_sphere_class_change_base_resp (transitivity E F) x.
Proof.
  apply (two_sphere_class_eq X d).
  change (x.1 ≈S x.1). reflexivity.
Defined.

(** Any two equality witnesses give the same class map, without asserting
    equality of the witnesses themselves. *)

(** 任意两份相等见证给出同一类映射，不断言见证本身相等。 *)

Lemma two_sphere_class_change_base_witness {b c : X 0}
    (E F : b ≈S c) (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp E x ≈S
      two_sphere_class_change_base_resp F x.
Proof.
  apply (two_sphere_class_eq X c).
  change (x.1 ≈S x.1). reflexivity.
Defined.

(** Equal base vertices give isomorphic class setoids after explicit common
    upward lifts. The inverse retains triangles as well. *)

(** 相等基点顶点的类广集在显式共同向上提升后同构；逆也保留三角形。 *)

Definition two_sphere_class_change_base_iso@{v q +}
    {b c : X 0} (E : b ≈S c)
  : LiftS@{_ _ v q} (TwoSphereClassS X b)
      ≅[SetCat@{v q _ _ _ _ _}] LiftS@{_ _ v q} (TwoSphereClassS X c).
Proof.
  exists ((two_sphere_class_change_base_resp E)^↑S),
    ((two_sphere_class_change_base_resp (symmetry E))^↑S).
  split; intros [x]; refine {|lower := _
                           |}; apply two_sphere_class_eq;
    change (x.1 ≈S x.1); reflexivity.
Defined.

(** Base equality also retains actual composition tetrahedra, changing
    only the constant zeroth face equation. *)

(** 基点相等也保留实际合成四面体，仅更换第零面的常值方程。 *)

Definition two_sphere_composite_change_base {b c : X 0} (E : b ≈S c)
    {x y z : TwoSphereS X b} (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite X c (two_sphere_change_base_resp E x)
      (two_sphere_change_base_resp E y) (two_sphere_change_base_resp E z).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]]. exists w.
  split; [| split; [| split]].
  - transitivity (simplex_constant X b 2); [exact H0 |].
    apply simplex_constant_vertex_eq. exact E.
  - exact H1.
  - exact H2.
  - exact H3.
Defined.

End SphereBaseEquality.

(** ** Functorial Maps on Classes

    Work at common ambient sizes with arbitrary simplicial maps. Naturality
    supplies boundary transport; existing generated descent supplies class
    respectfulness. Identity and composition laws use class equality. *)

(** ** 类上的函子性映射

    在共同环境大小中使用任意单纯映射。自然性提供边界运输，既有生成下降提供
    类的保相等性。恒等及复合定律使用类相等。 *)

(** Map the retained representative and every elementary generator. *)

(** 映射保留代表及每个初等生成元。 *)

Definition two_sphere_class_map_resp@{u p +}
    {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (α : X ⇒ Y) (b : X 0)
  : TwoSphereClassS X b →r TwoSphereClassS Y (α 0 b).
Proof.
  refine (two_sphere_class_desc X b
    (two_sphere_class_resp Y (α 0 b) ∘r two_sphere_map_resp α b) _).
  intros x y H. apply two_sphere_class_step.
  exact (two_sphere_homotopy_map α b H).
Defined.

(** The square commutes in class equality. The left arrow keeps each
    triangle while transporting its boundary from b to c; the right arrow
    uses the image equality under the degree-zero component of α. *)

(** 此方块按类相等交换。左箭头保持每个三角形，将其边界从 b 运输到 c；
    右箭头使用 α 的零维分量给出的像相等。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereClass}_2(X,b)
  \arrow[r,"{\alpha_*}"] \arrow[d,"{E_*}"'] &
\operatorname{SphereClass}_2(Y,\alpha_0 b)
  \arrow[d,"{(\alpha_0 E)_*}"] \\
\operatorname{SphereClass}_2(X,c) \arrow[r,"{\alpha_*}"'] &
\operatorname{SphereClass}_2(Y,\alpha_0 c)
\end{tikzcd}
\end{center}%
*)

(** ** Coherent Class-Map Laws

    Fix three arbitrary simplicial setoids at independent ambient bounds.
    Compare maps only after aligning their image bases by the specified
    equality; no Kan choices enter the laws. *)

(** ** 相干类映射定律

    在独立环境界固定任意三个单纯广集。只在用指定相等对齐像基点后比较映射；
    定律不带 Kan 选择。 *)

Section SphereClassMaps.
Universes u p.
Context {X Y Z : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.

(** The distinguished class goes to the distinguished image class. *)

(** 指定类送到像基点处的指定类。 *)

Lemma two_sphere_class_map_base (α : X ⇒ Y) (b : X 0)
  : two_sphere_class_map_resp α b (two_sphere_base X b) ≈S
      two_sphere_base Y (α 0 b).
Proof. apply two_sphere_class_eq. apply simplex_constant_natural. Defined.

(** The identity map acts as identity on classes. *)

(** 恒等映射在类上作用为恒等。 *)

Lemma two_sphere_class_map_id (b : X 0) (x : TwoSphereClassS X b)
  : two_sphere_class_map_resp idN b x ≈S x.
Proof.
  apply two_sphere_class_eq.
  change (x.1 ≈S x.1). reflexivity.
Defined.

(** Composition agrees with successive class maps at the same image base. *)

(** 复合与相继的类映射在同一个像基点处一致。 *)

Lemma two_sphere_class_map_comp (α : X ⇒ Y) (β : Y ⇒ Z)
    (b : X 0) (x : TwoSphereClassS X b)
  : two_sphere_class_map_resp (β ∘Nv α) b x ≈S
      two_sphere_class_map_resp β (α 0 b) (two_sphere_class_map_resp α b x).
Proof.
  apply two_sphere_class_eq.
  change (β 2 (α 2 x.1) ≈S β 2 (α 2 x.1)). reflexivity.
Defined.

(** Naturality of equality transport: map then change base, or change base
    then map. No comparison of transported membership records is required. *)

(** 相等运输的自然性：先映射再换基点，或先换基点再映射，无需比较运输后的
    隶属记录。 *)

Lemma two_sphere_class_map_change_base (α : X ⇒ Y) {b c : X 0}
    (E : b ≈S c) (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp Y (@func_proper _ _ (α 0) _ _ E)
      (two_sphere_class_map_resp α b x) ≈S
      two_sphere_class_map_resp α c (two_sphere_class_change_base_resp X E x).
Proof.
  apply two_sphere_class_eq.
  change (α 2 x.1 ≈S α 2 x.1). reflexivity.
Defined.

(** Naturally equal maps agree on classes after the explicit vertex
    equality from their degree-zero component is used. *)

(** 自然相等的映射在显式使用其零维分量给出的顶点相等后，在类上作用一致。 *)

Lemma two_sphere_class_map_eq {α β : X ⇒ Y} (E : α ≈N β)
    (b : X 0) (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp Y (E 0 b)
      (two_sphere_class_map_resp α b x) ≈S two_sphere_class_map_resp β b x.
Proof. apply two_sphere_class_eq. exact (E 2 x.1). Defined.

(** An actual tetrahedron composition is sent to its image tetrahedron,
    independently of whether either class setoid has a group operation. *)

(** 实际四面体合成送到其像四面体，与任一类广集是否具有群运算无关。 *)

Definition two_sphere_composite_map (α : X ⇒ Y) (b : X 0)
    {x y z : TwoSphereS X b} (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite Y (α 0 b)
      (two_sphere_map_resp α b x) (two_sphere_map_resp α b y)
      (two_sphere_map_resp α b z).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]]. exists (α 3 w).
  assert (E : ∀ i : Ordinal 3,
      d[Y; 2; i] (α 3 w) ≈S α 2 (d[X; 2; i] w)).
  { intros i. symmetry. apply simplex_face_natural. }
  split; [| split; [| split]].
  - transitivity (α 2 (d[X; 2; fin_first] w)); [apply E |].
    transitivity (α 2 (simplex_constant X b 2)).
    + apply func_proper. exact H0.
    + apply simplex_constant_natural.
  - transitivity (α 2 (d[X; 2; fin_first⁺] w)); [apply E |].
    apply func_proper. exact H1.
  - transitivity (α 2 (d[X; 2; fin_first⁺⁺] w)); [apply E |].
    apply func_proper. exact H2.
  - transitivity (α 2 (d[X; 2; fin_first⁺⁺⁺] w)); [apply E |].
    apply func_proper. exact H3.
Defined.

End SphereClassMaps.

(** ** Natural Isomorphisms Preserve Sphere-Class Setoids

    Fix a natural isomorphism and a source base vertex. Its inverse first
    lands at an inverse-image base vertex, then uses the component inverse
    equation to return to the original base. Both maps are transparent.
    Common upward lifts contain the retained class derivations; no resizing
    or equality of functors is required. This compares natural isomorphisms,
    not arbitrary homotopy or weak equivalences. *)

(** ** 自然同构保持球面类广集

    固定自然同构及源基点顶点。其逆先落到逆像基点，再用分量互逆方程返回
    原基点。两个映射均透明。共同向上提升容纳保留类推导，不要求大小重设或
    函子相等。此处比较自然同构，不比较任意同伦等价或弱等价。 *)

Section SphereClassIsomorphism.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (α : X ⇒ Y) (Hα : α ⦂ X ≅N Y) (b : X 0).

(** The inverse class map includes its explicit basepoint correction. *)

(** 逆类映射包含其显式基点校正。 *)

Definition two_sphere_class_inverse_resp
  : TwoSphereClassS Y (α 0 b) →r TwoSphereClassS X b
  := two_sphere_class_change_base_resp X (fst (Hα 0).2 b) ∘r
      two_sphere_class_map_resp (α ^-1N Hα) (α 0 b).

(** The corrected inverse recovers each original source class. *)

(** 校正后的逆恢复每个源类。 *)

Lemma two_sphere_class_inverse_l (x : TwoSphereClassS X b)
  : two_sphere_class_inverse_resp (two_sphere_class_map_resp α b x) ≈S x.
Proof. apply two_sphere_class_eq. exact (fst (Hα 2).2 x.1). Defined.

(** The forward map recovers every target class after the corrected inverse. *)

(** 校正取逆后，正向映射恢复每个目标类。 *)

Lemma two_sphere_class_inverse_r (y : TwoSphereClassS Y (α 0 b))
  : two_sphere_class_map_resp α b (two_sphere_class_inverse_resp y) ≈S y.
Proof. apply two_sphere_class_eq. exact (snd (Hα 2).2 y.1). Defined.

(** The resulting class-setoid isomorphism uses the same two maps and laws. *)

(** 所得类广集同构使用相同的两个映射及定律。 *)

Definition two_sphere_class_iso@{v q +}
  : LiftS@{_ _ v q} (TwoSphereClassS X b)
      ≅[SetCat@{v q _ _ _ _ _}] LiftS@{_ _ v q} (TwoSphereClassS Y (α 0 b)).
Proof.
  exists ((two_sphere_class_map_resp α b)^↑S),
    (two_sphere_class_inverse_resp^↑S). split.
  - intros [x]. exact {|lower := two_sphere_class_inverse_l x
                       |}.
  - intros [y]. exact {|lower := two_sphere_class_inverse_r y
                       |}.
Defined.

End SphereClassIsomorphism.
