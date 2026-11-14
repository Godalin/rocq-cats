From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereKan
  Instance.Set.Simplicial.FaceGluing.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Comparing Two Composite Fillers

    Two tetrahedra can have the same input faces without being equal as
    simplices. Their missing output faces must instead be compared by an
    actual sphere homotopy. The fourth dimension supplies that comparison.

    Given composite witnesses w and w', prescribe four tetrahedra of a
    four-simplex V: [d_0 V = b_3], [d_1 V = s_2 y], [d_3 V = w] and
    [d_4 V = w']. Their pairwise intersection triangles agree. Descend
    these faces using
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}%, then fill the actual horn with face two missing.
    Its omitted tetrahedron [d_2 V] has the two outputs as faces two and
    three, and constant faces zero and one. It is the required homotopy.

    This compares outputs for fixed input representatives. It does not
    yet descend composition through arbitrary generated input homotopies,
    prove group laws, or identify a general Kan homotopy group. Next,
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFirstTransport.SphereCompositeFirstHomotopy}
    {%[SphereCompositeFirstHomotopy]%}% transports a first-input homotopy
    while retaining the output representative. That module extends it
    through generated first-input equality, with the second input fixed. *)

(** * 比较两份合成填充

    两个四面体可以具有相同输入面，而不必是相等单形。应当用实际球面同伦
    比较其缺失输出面；第四维提供这一比较。

    给定合成见证 w、w'，指定四维单形 V 的四个四面体面：
    [d_0 V = b_3]、[d_1 V = s_2 y]、[d_3 V = w]、[d_4 V = w']。
    它们的逐对交叠三角形一致。经
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}% 下降，再填充缺失第二面的实际 horn。缺失四面体
    [d_2 V] 的第二、第三面是两个输出，第零、第一面为常值，因而给出所需同伦。

    这里比较固定输入代表的输出；尚未将合成沿任意生成输入同伦下降，未证明
    群律，也未识别一般 Kan 同伦群。接下来的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFirstTransport.SphereCompositeFirstHomotopy}
    {%[SphereCompositeFirstHomotopy]%}% 沿第一输入同伦运输并保留输出代表；
    该模块固定第二输入，将此运输扩展到第一输入的生成相等。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
w & V \arrow[l,"{d_3}"'] \arrow[r,"{d_4}"]
  \arrow[d,dashed,"{d_2}"'] & w' \\
& h \arrow[dl,"{d_2}"'] \arrow[dr,"{d_3}"] & \\
z && z'
\end{tikzcd}
\qquad $d_0V=b_3,\ d_1V=s_2y,\ d_0h=d_1h=b_2.$
\end{center}%
*)

(** ** Four Compatible Tetrahedra

    Fix a simplicial setoid with independent carrier and equality sizes
    and a base vertex. Degenerating y at position two gives two copies of
    y and two constant faces. These are the only degenerate faces needed
    to glue the comparison horn; no filler is selected here. *)

(** ** 四个相容四面体

    固定载体与相等大小独立的单纯广集及基点顶点。在位置二退化 y，得到两个
    y 面及两个常值面。比较 horn 的粘合只需要这些退化面，此处不选择填充。 *)

Section ComparisonFaces.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** The two low faces of the repeated sphere are constant. *)

(** 重复球面的两个低索引面为常值。 *)

Lemma sphere_comparison_degenerate_low (y : TwoSphereS X b)
    (i : Ordinal 1)
  : d[X; 2; i↑↑] (s[X; 2; fin_first⁺⁺] y.1) ≈S
      simplex_constant X b 2.
Proof.
  assert (H : fin_rank (i↑ : Ordinal 2) ≤
    fin_rank (fin_first⁺ : Ordinal 1)).
  { destruct i as [[] | [[] | []]]; cbn; repeat constructor. }
  transitivity (s[X; 1; fin_first⁺] (d[X; 1; i↑] y.1)).
  - exact (simplex_face_degeneracy_before (X := X) i↑ fin_first⁺ H y.1).
  - transitivity (s[X; 1; fin_first⁺] (simplex_constant X b 1)).
    + apply func_proper. exact (y.2 i↑).
    + apply simplex_constant_restrict.
Defined.

(** Face two is a dummy; only indices zero, one, three and four are used. *)

(** 第二面为占位，只使用索引零、一、三、四。 *)

Definition sphere_comparison_faces (y : TwoSphereS X b)
    (w w' : X 3) (j : Ordinal 4)
  : X 3
  := match fin_rank j with
  | 1 => s[X; 2; fin_first⁺⁺] y.1
  | 3 => w
  | 4 => w'
  | _ => simplex_constant X b 3
  end.

(** The six intersections follow from the composite input equations and
    simplicial identities. No equation identifies the two output faces. *)

(** 六个交叠由合成输入方程及单纯恒等式导出，不以方程预先等同两个输出。 *)

Lemma sphere_comparison_faces_pairwise
    {x y z z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
    (j k : Ordinal 4) (Hj : ¬ j = fin_first⁺⁺)
    (Hk : ¬ k = fin_first⁺⁺) (E : ¬ j = k)
  : d[X; 2; coface_intersection_index j k E]
      (sphere_comparison_faces y H.1 K.1 j) ≈S
      d[X; 2; coface_intersection_index k j
        (λ F, E (symmetry F))]
        (sphere_comparison_faces y H.1 K.1 k).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]], K as [w' [K0 [K1 [K2 K3]]]].
  assert (A01 : d[X; 2; fin_first] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] (s[X; 2; fin_first⁺⁺] y.1)).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact (sphere_comparison_degenerate_low y fin_first). }
  assert (A03 : d[X; 2; fin_first⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] w).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact H0. }
  assert (A04 : d[X; 2; fin_first⁺⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] w').
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact K0. }
  assert (A13 : d[X; 2; fin_first⁺⁺]
      (s[X; 2; fin_first⁺⁺] y.1) ≈S d[X; 2; fin_first⁺] w).
  { transitivity y.1.
    - exact (simplex_face_degeneracy_id (X := X)
        (fin_first⁺⁺ : Ordinal 2) y.1).
    - symmetry. exact H1. }
  assert (A14 : d[X; 2; fin_first⁺⁺⁺]
      (s[X; 2; fin_first⁺⁺] y.1) ≈S d[X; 2; fin_first⁺] w').
  { transitivity y.1.
    - exact (simplex_face_degeneracy_next (X := X)
        (fin_first⁺⁺ : Ordinal 2) y.1).
    - symmetry. exact K1. }
  assert (A34 : d[X; 2; fin_first⁺⁺⁺] w ≈S
    d[X; 2; fin_first⁺⁺⁺] w').
  { transitivity x.1; [exact H3 | symmetry; exact K3]. }
  destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]],
    k as [[] | [[] | [[] | [[] | [[] | []]]]]];
    try solve [destruct (Hj eq_refl) | destruct (Hk eq_refl) |
      destruct (E eq_refl)].
  all: first [exact A01 | exact A03 | exact A04 | exact A13 |
    exact A14 | exact A34 | exact (symmetry A01) | exact (symmetry A03) |
    exact (symmetry A04) | exact (symmetry A13) | exact (symmetry A14) |
    exact (symmetry A34)].
Defined.

(** Descend the four prescribed faces to an actual four-dimensional horn.
    The two composite witnesses may come from unrelated filler choices. *)

(** 将四个给定面下降为实际四维 horn；两份合成见证可以来自无关的填充选择。 *)

Definition SphereCompositeComparisonHornN
    {x y z z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
  : HornS X 4 fin_first⁺⁺
  := HornFacesN X 2 fin_first⁺⁺
      (sphere_comparison_faces y H.1 K.1)
      (sphere_comparison_faces_pairwise H K).

(** A filler recovers every prescribed retained tetrahedron. *)

(** 填充恢复每个给定的保留四面体。 *)

Lemma sphere_comparison_filler_face
    {x y z z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
    (V : X 4) (HV : is_horn_filler (SphereCompositeComparisonHornN H K) V)
    (j : Ordinal 4) (Hj : ¬ j = fin_first⁺⁺)
  : d[X; 3; j] V ≈S sphere_comparison_faces y H.1 K.1 j.
Proof.
  transitivity (face[fin_first⁺⁺; j; Hj]
    (SphereCompositeComparisonHornN H K)).
  - exact (fst (horn_filler_faces_iff _ V) HV j Hj).
  - apply horn_faces_β.
Defined.

(** Read the omitted tetrahedron, retaining all four homotopy equations.
    Only an actual filler equation is used; no selection is required. *)

(** 读出缺失四面体，保留全部四个同伦方程；仅使用实际填充方程，不要求选择。 *)

Definition SphereCompositeHomotopyOfFiller
    {x y z z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
    (V : X 4) (HV : is_horn_filler (SphereCompositeComparisonHornN H K) V)
  : TwoSphereHomotopy X b z z'.
Proof.
  exists (d[X; 3; fin_first⁺⁺] V). split; [| split; [| split]].
  - transitivity (d[X; 2; fin_first⁺] (d[X; 3; fin_first] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first : Ordinal 3) fin_first⁺ ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺] (simplex_constant X b 3)).
      * apply func_proper. exact (sphere_comparison_filler_face H K V HV
          fin_first ltac:(intros E; discriminate E)).
      * apply simplex_constant_restrict.
  - transitivity (d[X; 2; fin_first⁺] (d[X; 3; fin_first⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺]
        (s[X; 2; fin_first⁺⁺] y.1)).
      * apply func_proper. exact (sphere_comparison_filler_face H K V HV
          fin_first⁺ ltac:(intros E; discriminate E)).
      * exact (sphere_comparison_degenerate_low y fin_first⁺).
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] H.1).
      * apply func_proper. exact (sphere_comparison_filler_face H K V HV
          fin_first⁺⁺⁺ ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd H.2))).
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] K.1).
      * apply func_proper. exact (sphere_comparison_filler_face H K V HV
          fin_first⁺⁺⁺⁺ ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd K.2))).
Defined.

End ComparisonFaces.

(** ** Choosing the Comparison, Not Equating Fillers

    Fix the same independent sizes and basepoint. Only missing-face-two
    fillers in dimension four are assumed. Supplied composite tetrahedra
    need no chosen three-dimensional filler structure. The elementary
    homotopy below is retained before passing to generated class equality. *)

(** ** 选择比较，而非等同填充

    固定同样的独立大小及基点，只假设四维缺失第二面的填充。给定的合成
    四面体不要求选定三维填充结构。先保留下述初等同伦，再转为生成类相等。 *)

Section ChosenComparison.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX : !HasHornFillers X 4 fin_first⁺⁺}.

(** Any two composites of the same representatives have elementarily
    homotopic outputs, using the actual selected four-horn filler. *)

(** 相同代表的任意两个合成，其输出由实际选定四维 horn 填充给出初等同伦。 *)

Definition SphereCompositeOutputHomotopy
    {x y z z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
  : TwoSphereHomotopy X b z z'.
Proof.
  pose (V := horn_fill (SphereCompositeComparisonHornN X b H K)).
  exact (SphereCompositeHomotopyOfFiller X b H K V.1 V.2).
Defined.

(** The output class is independent of which composite tetrahedron was
    supplied; this does not identify their original triangles. *)

(** 输出类与给定哪份合成四面体无关，不等同其原始三角形。 *)

Lemma two_sphere_composite_output_eq
    {x y z z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x y z')
  : (z : TwoSphereClassS X b) ≈S z'.
Proof.
  exact (two_sphere_class_step X b (SphereCompositeOutputHomotopy H K)).
Defined.

(** Input replacement uses only the original specified sphere equality.
    Arbitrary generated sphere homotopies are not covered by this law. *)

(** 输入替换仅使用球面原有指定相等；本律尚不覆盖任意生成球面同伦。 *)

Lemma two_sphere_composite_output_eq_inputs
    {x y z x' y' z' : TwoSphereS X b}
    (H : TwoSphereComposite X b x y z)
    (K : TwoSphereComposite X b x' y' z')
    (E : x ≈S x') (F : y ≈S y')
  : (z : TwoSphereClassS X b) ≈S z'.
Proof.
  exact (two_sphere_composite_output_eq
    (TwoSphereCompositeChangeEndpoints X b H E F (reflexivity z)) K).
Defined.

(** Independent three-horn selections give the same output class. Neither
    of them is required to preserve horn equality, and they are never equated. *)

(** 独立三维 horn 选择给出相同输出类；不要求任一选择保持 horn 相等，也不等同
    两个选择。 *)

Lemma two_sphere_kan_composite_choice_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS X b)
  : ((@SphereKanComposite X b H x y).1 : TwoSphereClassS X b) ≈S
      (@SphereKanComposite X b K x y).1.
Proof.
  exact (two_sphere_composite_output_eq
    (@SphereKanComposite X b H x y).2 (@SphereKanComposite X b K x y).2).
Defined.

(** The same comparison respects specified equality in both inputs,
    even when the two composite selections are unrelated. *)

(** 即使两个合成选择无关，同一比较也保持两个输入的指定相等。 *)

Lemma two_sphere_kan_composite_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    {x y x' y' : TwoSphereS X b} (E : x ≈S x') (F : y ≈S y')
  : ((@SphereKanComposite X b H x y).1 : TwoSphereClassS X b) ≈S
      (@SphereKanComposite X b K x' y').1.
Proof.
  exact (two_sphere_composite_output_eq_inputs
    (@SphereKanComposite X b H x y).2
    (@SphereKanComposite X b K x' y').2 E F).
Defined.

End ChosenComparison.
