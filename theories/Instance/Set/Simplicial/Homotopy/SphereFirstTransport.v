From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereKanComparison.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Transporting the First Composite Input

    Suppose a tetrahedron h gives an elementary homotopy from x to x'.
    A composite of x with y can be replaced by a composite of x' with y,
    keeping the very same output triangle z. The new tetrahedron comes
    from a four-dimensional horn, not from equality of x and x'. Face
    equations use specified equality; z itself is retained as input data.

    Prescribe [d_0 V = b_3], [d_1 V = s_1 y], [d_2 V = w] and
    [d_4 V = h]. Filling face three produces the new composite. Conversely,
    place a composite of x' at face three and fill face two to return to x.
    Pairwise descent from
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}% supplies the actual horn maps in both directions.

    This is a prerequisite for class descent in the first input. Transport
    in the second input and a binary operation on sphere classes require
    further work. No group law or general homotopy-group identification is
    claimed here. In the diagram, the top arrow is the supplied elementary
    homotopy h; the dashed arrow is the constructed replacement of a
    composite. Vertical arrows read faces in specified equality. *)

(** * 运输合成的第一输入

    设四面体 h 给出从 x 到 x' 的初等同伦。可以将 x 与 y 的一份合成替换为
    x' 与 y 的合成，保留完全相同的输出三角形 z。新四面体来自四维 horn，
    而非来自 x 与 x' 的相等。面方程使用指定相等，z 本身保留为输入数据。

    指定 [d_0 V = b_3]、[d_1 V = s_1 y]、[d_2 V = w]、[d_4 V = h]，
    填充第三面即得到新合成。反向则把 x' 的合成放在第三面，填充第二面返回 x。
    两个方向均经
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}% 的逐对下降得到实际 horn 映射。

    这是第一输入类上下降的前置；第二输入运输和球面类上的二元运算仍需后续
    工作，此处不声称群律或一般同伦群识别。下图顶边表示给定初等同伦 h，虚线
    表示构造的合成替换，竖边按指定相等读出各面。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
x \arrow[r,"h"] & x' \\
w \arrow[u,"d_3"] \arrow[r,dashed] \arrow[d,"d_2"']
  & w' \arrow[u,"d_3"'] \arrow[d,"d_2"] \\
z \arrow[r,equal] & z
\end{tikzcd}
\qquad $d_0w=d_0w'=b_2,\quad d_1w=d_1w'=y.$
\end{center}%
*)

(** ** One Face Table for Both Directions

    Fix a simplicial setoid with independent sizes and a base vertex.
    The same supplied tetrahedron is placed at positions two and three;
    one of these positions is omitted in each application. Its placeholder
    imposes no condition on the filler. Endpoint agreements are required
    only at retained positions. *)

(** ** 两个方向共用的面表

    固定大小独立的单纯广集及基点。把同一个给定四面体放在第二、第三位置，
    每次应用省略其中一个；该占位项不对填充施加条件。只对保留位置要求端点
    一致。 *)

Section FirstTransportFaces.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Face zero of the middle degeneracy is constant. *)

(** 中间退化的第零面为常值。 *)

Lemma sphere_first_degenerate_zero (y : TwoSphereS X b)
  : d[X; 2; fin_first] (s[X; 2; fin_first⁺] y.1) ≈S
      simplex_constant X b 2.
Proof.
  transitivity (s[X; 1; fin_first] (d[X; 1; fin_first] y.1)).
  - exact (simplex_face_degeneracy_before (X := X)
      (fin_first : Ordinal 2) fin_first ltac:(cbn; repeat constructor) y.1).
  - transitivity (s[X; 1; fin_first] (simplex_constant X b 1)).
    + apply func_proper. exact (y.2 fin_first).
    + apply simplex_constant_restrict.
Defined.

(** Its last face is also constant. *)

(** 其最后一个面也为常值。 *)

Lemma sphere_first_degenerate_last (y : TwoSphereS X b)
  : d[X; 2; fin_first⁺⁺⁺] (s[X; 2; fin_first⁺] y.1) ≈S
      simplex_constant X b 2.
Proof.
  transitivity (s[X; 1; fin_first⁺] (d[X; 1; fin_first⁺⁺] y.1)).
  - exact (simplex_face_degeneracy_after (X := X)
      (fin_first⁺⁺ : Ordinal 2) fin_first⁺
      ltac:(cbn; repeat constructor) y.1).
  - transitivity (s[X; 1; fin_first⁺] (simplex_constant X b 1)).
    + apply func_proper. exact (y.2 fin_first⁺⁺).
    + apply simplex_constant_restrict.
Defined.

(** Only one of the two occurrences of w is retained in each transport. *)

(** 每个运输仅保留 w 的两次出现之一。 *)

Definition sphere_first_transport_faces (y : TwoSphereS X b)
    (w h : X 3) (j : Ordinal 4)
  : X 3
  := match fin_rank j with
  | 1 => s[X; 2; fin_first⁺] y.1
  | 2 => w
  | 3 => w
  | 4 => h
  | _ => simplex_constant X b 3
  end.

(** Retained endpoint agreements give all pairwise intersections. The
    output face of the supplied composite is not used in this gluing. *)

(** 保留端点的一致给出全部逐对交叠；粘合不使用给定合成的输出面。 *)

Lemma sphere_first_transport_faces_pairwise
    {t x x' y z : TwoSphereS X b}
    (H : TwoSphereComposite X b t y z)
    (G : TwoSphereHomotopy X b x x') (i : Ordinal 4)
    (E2 : ¬ fin_first⁺⁺ = i → t ≈S x)
    (E3 : ¬ fin_first⁺⁺⁺ = i → t ≈S x')
    (j k : Ordinal 4) (Hj : ¬ j = i) (Hk : ¬ k = i) (E : ¬ j = k)
  : d[X; 2; coface_intersection_index j k E]
      (sphere_first_transport_faces y H.1 G.1 j) ≈S
      d[X; 2; coface_intersection_index k j (λ F, E (symmetry F))]
        (sphere_first_transport_faces y H.1 G.1 k).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]], G as [h [G0 [G1 [G2 G3]]]].
  assert (A01 : d[X; 2; fin_first] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] (s[X; 2; fin_first⁺] y.1)).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. apply sphere_first_degenerate_zero. }
  assert (A02 : d[X; 2; fin_first⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] w).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact H0. }
  assert (A03 : d[X; 2; fin_first⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] w).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact H0. }
  assert (A04 : d[X; 2; fin_first⁺⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] h).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact G0. }
  assert (A12 : d[X; 2; fin_first⁺] (s[X; 2; fin_first⁺] y.1) ≈S
    d[X; 2; fin_first⁺] w).
  { transitivity y.1.
    - exact (simplex_face_degeneracy_id (X := X)
        (fin_first⁺ : Ordinal 2) y.1).
    - symmetry. exact H1. }
  assert (A13 : d[X; 2; fin_first⁺⁺] (s[X; 2; fin_first⁺] y.1) ≈S
    d[X; 2; fin_first⁺] w).
  { transitivity y.1.
    - exact (simplex_face_degeneracy_next (X := X)
        (fin_first⁺ : Ordinal 2) y.1).
    - symmetry. exact H1. }
  assert (A14 : d[X; 2; fin_first⁺⁺⁺] (s[X; 2; fin_first⁺] y.1) ≈S
    d[X; 2; fin_first⁺] h).
  { transitivity (simplex_constant X b 2).
    - apply sphere_first_degenerate_last.
    - symmetry. exact G1. }
  assert (A24 : ¬ fin_first⁺⁺ = i →
    d[X; 2; fin_first⁺⁺⁺] w ≈S d[X; 2; fin_first⁺⁺] h).
  { intros R. transitivity t.1; [exact H3 |].
    transitivity x.1; [exact (E2 R) | symmetry; exact G2]. }
  assert (A34 : ¬ fin_first⁺⁺⁺ = i →
    d[X; 2; fin_first⁺⁺⁺] w ≈S d[X; 2; fin_first⁺⁺⁺] h).
  { intros R. transitivity t.1; [exact H3 |].
    transitivity x'.1; [exact (E3 R) | symmetry; exact G3]. }
  destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]],
    k as [[] | [[] | [[] | [[] | [[] | []]]]]];
    try solve [destruct (E eq_refl)].
  all: first [exact A01 | exact A02 | exact A03 | exact A04 |
    exact A12 | exact A13 | exact A14 | exact (A24 Hj) | exact (A34 Hj) |
    exact (symmetry A01) | exact (symmetry A02) | exact (symmetry A03) |
    exact (symmetry A04) | exact (symmetry A12) | exact (symmetry A13) |
    exact (symmetry A14) | exact (symmetry (A24 Hk)) |
    exact (symmetry (A34 Hk)) | reflexivity].
Defined.

(** Descend the shared table, keeping endpoint evidence only where needed. *)

(** 下降共用面表，仅在需要处保留端点证据。 *)

Definition SphereFirstTransportHornN
    {t x x' y z : TwoSphereS X b}
    (H : TwoSphereComposite X b t y z)
    (G : TwoSphereHomotopy X b x x') (i : Ordinal 4)
    (E2 : ¬ fin_first⁺⁺ = i → t ≈S x)
    (E3 : ¬ fin_first⁺⁺⁺ = i → t ≈S x')
  : HornS X 4 i
  := HornFacesN X 2 i (sphere_first_transport_faces y H.1 G.1)
      (sphere_first_transport_faces_pairwise H G i E2 E3).

(** Forward transport leaves the third tetrahedron missing. *)

(** 正向运输省略第三四面体面。 *)

Definition SphereFirstForwardHornN
    {x x' y z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x y z)
  : HornS X 4 fin_first⁺⁺⁺
  := SphereFirstTransportHornN H G fin_first⁺⁺⁺
      (λ _, reflexivity x) (λ R, match R eq_refl with end).

(** Backward transport leaves the second tetrahedron missing. *)

(** 反向运输省略第二四面体面。 *)

Definition SphereFirstBackwardHornN
    {x x' y z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x' y z)
  : HornS X 4 fin_first⁺⁺
  := SphereFirstTransportHornN H G fin_first⁺⁺
      (λ R, match R eq_refl with end) (λ _, reflexivity x').

(** A filler recovers each retained tetrahedron of the shared table. *)

(** 填充恢复共用面表的每个保留四面体。 *)

Lemma sphere_first_transport_filler_face
    {t x x' y z : TwoSphereS X b}
    (H : TwoSphereComposite X b t y z)
    (G : TwoSphereHomotopy X b x x') (i : Ordinal 4)
    (E2 : ¬ fin_first⁺⁺ = i → t ≈S x)
    (E3 : ¬ fin_first⁺⁺⁺ = i → t ≈S x')
    (V : X 4) (HV : is_horn_filler (SphereFirstTransportHornN H G i E2 E3) V)
    (j : Ordinal 4) (Hj : ¬ j = i)
  : d[X; 3; j] V ≈S sphere_first_transport_faces y H.1 G.1 j.
Proof.
  transitivity (face[i; j; Hj] (SphereFirstTransportHornN H G i E2 E3)).
  - exact (fst (horn_filler_faces_iff _ V) HV j Hj).
  - apply horn_faces_β.
Defined.

End FirstTransportFaces.

(** ** Reading Transported Composites from Supplied Fillers

    Fix the same simplicial setoid and vertex. A supplied filler equation
    suffices in either direction, without selecting any Kan structure.
    The returned tetrahedron keeps the original output representative. *)

(** ** 从给定填充读出运输后的合成

    固定同样的单纯广集及顶点。每个方向只需给定填充方程，不选择 Kan 结构。
    返回四面体保留原有输出代表。 *)

Section GivenFirstTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Missing face three composes x' with y and keeps output z. *)

(** 缺失第三面合成 x' 与 y，保留输出 z。 *)

Definition SphereCompositeFirstOfFiller
    {x x' y z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x y z)
    (V : X 4) (HV : is_horn_filler (SphereFirstForwardHornN X b G H) V)
  : TwoSphereComposite X b x' y z.
Proof.
  assert (F : ∀ j (Hj : ¬ j = fin_first⁺⁺⁺),
    d[X; 3; j] V ≈S sphere_first_transport_faces X b y H.1 G.1 j).
  { intros j Hj. exact (sphere_first_transport_filler_face X b H G
      fin_first⁺⁺⁺ (λ _, reflexivity x)
      (λ R, match R eq_refl with end) V HV j Hj). }
  exists (d[X; 3; fin_first⁺⁺⁺] V). split; [| split; [| split]].
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] (simplex_constant X b 3)).
      * apply func_proper. exact (F fin_first
          ltac:(intros E; discriminate E)).
      * apply simplex_constant_restrict.
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] (s[X; 2; fin_first⁺] y.1)).
      * apply func_proper. exact (F fin_first⁺
          ltac:(intros E; discriminate E)).
      * exact (simplex_face_degeneracy_next (X := X)
          (fin_first⁺ : Ordinal 2) y.1).
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] H.1).
      * apply func_proper. exact (F fin_first⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd H.2))).
  - transitivity (d[X; 2; fin_first⁺⁺⁺] (d[X; 3; fin_first⁺⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺⁺⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺⁺] G.1).
      * apply func_proper. exact (F fin_first⁺⁺⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (snd (snd (snd G.2))).
Defined.

(** Missing face two returns to x, still keeping output z. *)

(** 缺失第二面返回 x，仍保留输出 z。 *)

Definition SphereCompositeFirstBackOfFiller
    {x x' y z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x' y z)
    (V : X 4) (HV : is_horn_filler (SphereFirstBackwardHornN X b G H) V)
  : TwoSphereComposite X b x y z.
Proof.
  assert (F : ∀ j (Hj : ¬ j = fin_first⁺⁺),
    d[X; 3; j] V ≈S sphere_first_transport_faces X b y H.1 G.1 j).
  { intros j Hj. exact (sphere_first_transport_filler_face X b H G
      fin_first⁺⁺ (λ R, match R eq_refl with end)
      (λ _, reflexivity x') V HV j Hj). }
  exists (d[X; 3; fin_first⁺⁺] V). split; [| split; [| split]].
  - transitivity (d[X; 2; fin_first⁺] (d[X; 3; fin_first] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first : Ordinal 3) fin_first⁺ ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺] (simplex_constant X b 3)).
      * apply func_proper. exact (F fin_first
          ltac:(intros E; discriminate E)).
      * apply simplex_constant_restrict.
  - transitivity (d[X; 2; fin_first⁺] (d[X; 3; fin_first⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺] (s[X; 2; fin_first⁺] y.1)).
      * apply func_proper. exact (F fin_first⁺
          ltac:(intros E; discriminate E)).
      * exact (simplex_face_degeneracy_id (X := X)
          (fin_first⁺ : Ordinal 2) y.1).
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] H.1).
      * apply func_proper. exact (F fin_first⁺⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd H.2))).
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] G.1).
      * apply func_proper. exact (F fin_first⁺⁺⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd G.2))).
Defined.

End GivenFirstTransport.

(** ** Chosen Elementary Transports

    Fix the ambient setoid and vertex. Each direction asks for only the
    four-horn selection it uses: face three forward and face two backward.
    Neither direction assumes full Kan or respectful filler choices. *)

(** ** 选定初等运输

    固定环境广集及顶点。每个方向只要求自身使用的四维 horn 选择：正向缺第三
    面，反向缺第二面。不要求完整 Kan 或填充选择保相等。 *)

Section ChosenFirstTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Transport a composite along one elementary first-input homotopy. *)

(** 沿第一输入的一次初等同伦运输合成。 *)

Definition SphereCompositeFirstHomotopy
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺}
    {x x' y z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite X b x' y z.
Proof.
  pose (V := horn_fill (SphereFirstForwardHornN X b G H)).
  exact (SphereCompositeFirstOfFiller X b G H V.1 V.2).
Defined.

(** Return along that same homotopy, without first reversing the
    homotopy tetrahedron or identifying its witnesses. *)

(** 沿同一个同伦返回，无须先反转同伦四面体或等同其见证。 *)

Definition SphereCompositeFirstHomotopyBack
    `{HX : !HasHornFillers X 4 fin_first⁺⁺}
    {x x' y z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b x x') (H : TwoSphereComposite X b x' y z)
  : TwoSphereComposite X b x y z.
Proof.
  pose (V := horn_fill (SphereFirstBackwardHornN X b G H)).
  exact (SphereCompositeFirstBackOfFiller X b G H V.1 V.2).
Defined.

End ChosenFirstTransport.

(** ** Folding Generated First-Input Equality

    Fix both required four-horn selections. Two-way transport on the
    original specified equality and elementary homotopy generators extends
    to their existing equivalence closure. Reuse [equiv_closure_preserves],
    with Type-valued two-way implication between composite witness types;
    no new closure induction or resizing of witnesses is introduced. The
    two witness transformations carry no inverse equations on tetrahedra. *)

(** ** 折叠第一输入的生成相等

    固定两个所需四维 horn 选择。原有指定相等及初等同伦生成元上的双向运输
    扩展到既有等价闭包。复用 [equiv_closure_preserves]，以合成见证类型之间的
    Type 值双向蕴含为目标，不重建闭包归纳，也不重设见证大小。这两个见证
    转换不带有四面体上的互逆方程。 *)

Section FirstClassTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.

(** Class-equal first inputs give two transparent transformations between
    composite witnesses, keeping the other input and output fixed. *)

(** 第一输入的类相等给出合成见证间两个透明转换，固定另一输入及输出。 *)

Definition two_sphere_composite_first_class
    {x x' : TwoSphereS X b} (E : (x : TwoSphereClassS X b) ≈S x')
    (y z : TwoSphereS X b)
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x' y z.
Proof.
  refine (@equiv_closure_preserves _ _ _ iffT _
    (λ a, TwoSphereComposite X b a y z) _ x x' E).
  - split; typeclasses eauto.
  - intros a a' [F | G].
    + split; intros H.
      * exact (TwoSphereCompositeChangeEndpoints X b H F
          (reflexivity y) (reflexivity z)).
      * exact (TwoSphereCompositeChangeEndpoints X b H (symmetry F)
          (reflexivity y) (reflexivity z)).
    + split; intros H.
      * exact (SphereCompositeFirstHomotopy X b G H).
      * exact (SphereCompositeFirstHomotopyBack X b G H).
Defined.

(** Arbitrary generated first-input equality preserves the selected output
    class, even for two independent three-horn selections. *)

(** 第一输入的任意生成相等保持选定输出类，即使两个三维 horn 选择相互独立。 *)

Lemma two_sphere_kan_composite_first_class_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    {x x' : TwoSphereS X b} (E : (x : TwoSphereClassS X b) ≈S x')
    (y : TwoSphereS X b)
  : ((@SphereKanComposite X b H x y).1 : TwoSphereClassS X b) ≈S
      (@SphereKanComposite X b K x' y).1.
Proof.
  exact (two_sphere_composite_output_eq X b
    (fst (two_sphere_composite_first_class E y
      (@SphereKanComposite X b H x y).1)
      (@SphereKanComposite X b H x y).2)
    (@SphereKanComposite X b K x' y).2).
Defined.

(** For a fixed second-input representative, composition descends in its
    first input to an actual respectful map on sphere classes. *)

(** 固定第二输入代表，合成对第一输入下降为球面类上的实际保相等映射。 *)

Program Definition two_sphere_kan_composite_first_resp
    (H : HasHornFillers X 3 fin_first⁺⁺) (y : TwoSphereS X b)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  :=
  {|func x := (@SphereKanComposite X b H x y).1
  |}.
Next Obligation.
  intros x x' E. exact (two_sphere_kan_composite_first_class_eq H H E y).
Defined.

(** The descended maps for two selections agree pointwise in specified
    class equality, without equality of functions or filler records. *)

(** 两个选择的下降映射按指定类相等逐点一致，不等同函数或填充记录。 *)

Lemma two_sphere_kan_composite_first_choice_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺) (y : TwoSphereS X b)
  : two_sphere_kan_composite_first_resp H y ≈f
      two_sphere_kan_composite_first_resp K y.
Proof.
  intros x. exact (two_sphere_kan_composite_choice_eq X b H K x y).
Defined.

End FirstClassTransport.
