From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereFirstTransport.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Transporting the Second Composite Input

    The first-input construction in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFirstTransport.SphereCompositeFirstHomotopy}
    {%[SphereCompositeFirstHomotopy]%}% keeps the second input fixed.
    Here h runs from y to y', and w composes x with y to output z.
    The face table [b_3, h, s_2 z, w, w] gives a different four-horn:
    omit face four to obtain a composite of x with y', or omit face three
    to return to y. Only retained occurrences of w impose conditions.
    In particular, the outer horn in the forward direction is required;
    an inner-horn assumption alone is not asserted to suffice.

    Both directions retain x and the very same output representative z.
    The diagram reads faces in specified equality. Its dashed arrow is
    constructed from the filler, not supplied as an equality of tetrahedra.
    After elementary transport, the existing equivalence-closure fold
    handles arbitrary generated second-input equality. This prerequisite
    does not itself package a binary class operation or prove group laws.
    The next chapter's
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereMagma.TwoSphereClassMagma}
    {%[TwoSphereClassMagma]%}% combines the two input transports into an
    explicitly chosen magma. *)

(** * 运输合成的第二输入

    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereFirstTransport.SphereCompositeFirstHomotopy}
    {%[SphereCompositeFirstHomotopy]%}% 的第一输入构造固定第二输入。
    此处 h 从 y 到 y'，w 将 x 与 y 合成为 z。面表 [b_3, h, s_2 z, w, w]
    给出另一四维 horn：省略第四面得到 x 与 y' 的合成，省略第三面则返回 y。
    仅对保留的 w 位置施加条件。正向确实要求外 horn，不声称只需内 horn。

    两个方向均保留 x 以及完全相同的输出代表 z。下图按指定相等读取各面，
    虚线由填充构造，不是给定四面体相等。初等运输之后，既有等价闭包折叠
    处理第二输入的任意生成相等。此前置自身不打包二元类运算或证明群律。
    下一章的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereMagma.TwoSphereClassMagma}
    {%[TwoSphereClassMagma]%}% 将两个输入运输组合为显式选定的原群。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
y \arrow[r,"h"] & y' \\
w \arrow[u,"d_1"] \arrow[r,dashed] \arrow[d,"d_2"']
  & w' \arrow[u,"d_1"'] \arrow[d,"d_2"] \\
z \arrow[r,equal] & z
\end{tikzcd}
\qquad $d_0w=d_0w'=b_2,\quad d_3w=d_3w'=x.$
\end{center}%
*)

(** ** A Shared Face Table

    Fix a simplicial setoid with independent carrier and equality sizes,
    and a base vertex. Only retained composite positions must agree with
    the corresponding endpoints of the supplied homotopy. *)

(** ** 共用面表

    固定载体与相等大小独立的单纯广集及基点。只有保留的合成位置，才须与给定
    同伦的相应端点一致。 *)

Section SecondTransportFaces.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** The duplicated composite is a placeholder at the omitted position. *)

(** 重复的合成在省略位置只是占位项。 *)

Definition sphere_second_transport_faces (z : TwoSphereS X b)
    (w h : X 3) (j : Ordinal 4)
  : X 3
  := match fin_rank j with
  | 1 => h
  | 2 => s[X; 2; fin_first⁺⁺] z.1
  | 3 => w
  | 4 => w
  | _ => simplex_constant X b 3
  end.

(** Pairwise intersections use endpoint agreement only when its face is
    retained. No equality of outputs or fillers is requested. *)

(** 逐对交叠只在保留相应面时使用端点一致；不要求输出或填充相等。 *)

Lemma sphere_second_transport_faces_pairwise
    {x t y y' z : TwoSphereS X b}
    (H : TwoSphereComposite X b x t z)
    (G : TwoSphereHomotopy X b y y') (i : Ordinal 4)
    (E3 : ¬ fin_first⁺⁺⁺ = i → t ≈S y)
    (E4 : ¬ fin_first⁺⁺⁺⁺ = i → t ≈S y')
    (j k : Ordinal 4) (Hj : ¬ j = i) (Hk : ¬ k = i) (E : ¬ j = k)
  : d[X; 2; coface_intersection_index j k E]
      (sphere_second_transport_faces z H.1 G.1 j) ≈S
      d[X; 2; coface_intersection_index k j (λ F, E (symmetry F))]
        (sphere_second_transport_faces z H.1 G.1 k).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]], G as [h [G0 [G1 [G2 G3]]]].
  assert (A01 : d[X; 2; fin_first] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] h).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact G0. }
  assert (A02 : d[X; 2; fin_first⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] (s[X; 2; fin_first⁺⁺] z.1)).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact (sphere_comparison_degenerate_low X b z fin_first). }
  assert (A03 : d[X; 2; fin_first⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] w).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact H0. }
  assert (A04 : d[X; 2; fin_first⁺⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] w).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact H0. }
  assert (A12 : d[X; 2; fin_first⁺] h ≈S
    d[X; 2; fin_first⁺] (s[X; 2; fin_first⁺⁺] z.1)).
  { transitivity (simplex_constant X b 2); [exact G1 |].
    symmetry. exact (sphere_comparison_degenerate_low X b z fin_first⁺). }
  assert (A13 : ¬ fin_first⁺⁺⁺ = i →
    d[X; 2; fin_first⁺⁺] h ≈S
    d[X; 2; fin_first⁺] w).
  { intros R. transitivity y.1; [exact G2 |].
    transitivity t.1; [symmetry; exact (E3 R) | symmetry; exact H1]. }
  assert (A14 : ¬ fin_first⁺⁺⁺⁺ = i →
    d[X; 2; fin_first⁺⁺⁺] h ≈S
    d[X; 2; fin_first⁺] w).
  { intros R. transitivity y'.1; [exact G3 |].
    transitivity t.1; [symmetry; exact (E4 R) | symmetry; exact H1]. }
  assert (A23 : d[X; 2; fin_first⁺⁺] (s[X; 2; fin_first⁺⁺] z.1) ≈S
    d[X; 2; fin_first⁺⁺] w).
  { transitivity z.1.
    - exact (simplex_face_degeneracy_id (X := X)
        (fin_first⁺⁺ : Ordinal 2) z.1).
    - symmetry. exact H2. }
  assert (A24 : d[X; 2; fin_first⁺⁺⁺] (s[X; 2; fin_first⁺⁺] z.1) ≈S
    d[X; 2; fin_first⁺⁺] w).
  { transitivity z.1.
    - exact (simplex_face_degeneracy_next (X := X)
        (fin_first⁺⁺ : Ordinal 2) z.1).
    - symmetry. exact H2. }
  destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]],
    k as [[] | [[] | [[] | [[] | [[] | []]]]]];
    try solve [destruct (E eq_refl)].
  all: first [exact A01 | exact A02 | exact A03 | exact A04 |
    exact A12 | exact (A13 Hk) | exact (A14 Hk) | exact A23 | exact A24 |
    exact (symmetry A01) | exact (symmetry A02) | exact (symmetry A03) |
    exact (symmetry A04) | exact (symmetry A12) |
    exact (symmetry (A13 Hj)) | exact (symmetry (A14 Hj)) |
    exact (symmetry A23) | exact (symmetry A24) | reflexivity].
Defined.

(** Descend the table to a genuine horn map using pairwise gluing. *)

(** 用逐对粘合将面表下降为真正的 horn 映射。 *)

Definition SphereSecondTransportHornN
    {x t y y' z : TwoSphereS X b}
    (H : TwoSphereComposite X b x t z)
    (G : TwoSphereHomotopy X b y y') (i : Ordinal 4)
    (E3 : ¬ fin_first⁺⁺⁺ = i → t ≈S y)
    (E4 : ¬ fin_first⁺⁺⁺⁺ = i → t ≈S y')
  : HornS X 4 i
  := HornFacesN X 2 i (sphere_second_transport_faces z H.1 G.1)
      (sphere_second_transport_faces_pairwise H G i E3 E4).

(** Forward transport omits face four; its placeholder is unconstrained. *)

(** 正向运输省略第四面，其占位项不受约束。 *)

Definition SphereSecondForwardHornN
    {x y y' z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y z)
  : HornS X 4 fin_first⁺⁺⁺⁺
  := SphereSecondTransportHornN H G fin_first⁺⁺⁺⁺
      (λ _, reflexivity y) (λ R, match R eq_refl with end).

(** Backward transport omits face three and retains the y' composite. *)

(** 反向运输省略第三面，保留 y' 的合成。 *)

Definition SphereSecondBackwardHornN
    {x y y' z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y' z)
  : HornS X 4 fin_first⁺⁺⁺
  := SphereSecondTransportHornN H G fin_first⁺⁺⁺
      (λ R, match R eq_refl with end) (λ _, reflexivity y').

(** Recover the retained tetrahedra from an actual filler equation. *)

(** 从实际填充方程恢复保留的四面体。 *)

Lemma sphere_second_transport_filler_face
    {x t y y' z : TwoSphereS X b}
    (H : TwoSphereComposite X b x t z)
    (G : TwoSphereHomotopy X b y y') (i : Ordinal 4)
    (E3 : ¬ fin_first⁺⁺⁺ = i → t ≈S y)
    (E4 : ¬ fin_first⁺⁺⁺⁺ = i → t ≈S y')
    (V : X 4)
    (HV : is_horn_filler (SphereSecondTransportHornN H G i E3 E4) V)
    (j : Ordinal 4) (Hj : ¬ j = i)
  : d[X; 3; j] V ≈S sphere_second_transport_faces z H.1 G.1 j.
Proof.
  transitivity (face[i; j; Hj] (SphereSecondTransportHornN H G i E3 E4)).
  - exact (fst (horn_filler_faces_iff _ V) HV j Hj).
  - apply horn_faces_β.
Defined.

End SecondTransportFaces.

(** ** Reading the Missing Composite

    With the same ambient simplicial setoid and vertex, a supplied actual
    filler suffices in either direction. No chosen Kan structure is needed.
    The missing tetrahedron retains the first input and output data. *)

(** ** 读出缺失合成

    固定同样的环境单纯广集及顶点，每个方向只需给定实际填充，不要求选定 Kan
    结构。缺失四面体保留第一输入及输出数据。 *)

Section GivenSecondTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Read the forward composite without changing x or z. *)

(** 读出正向合成，不改变 x 或 z。 *)

Definition SphereCompositeSecondOfFiller
    {x y y' z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y z)
    (V : X 4) (HV : is_horn_filler (SphereSecondForwardHornN X b G H) V)
  : TwoSphereComposite X b x y' z.
Proof.
  assert (F : ∀ j (Hj : ¬ j = fin_first⁺⁺⁺⁺),
    d[X; 3; j] V ≈S sphere_second_transport_faces X b z H.1 G.1 j).
  { intros j Hj. exact (sphere_second_transport_filler_face X b H G
      fin_first⁺⁺⁺⁺ (λ _, reflexivity y)
      (λ R, match R eq_refl with end) V HV j Hj). }
  exists (d[X; 3; fin_first⁺⁺⁺⁺] V). split; [| split; [| split]].
  - transitivity (d[X; 2; fin_first⁺⁺⁺] (d[X; 3; fin_first] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺⁺] (simplex_constant X b 3)).
      * apply func_proper. exact (F fin_first
          ltac:(intros E; discriminate E)).
      * apply simplex_constant_restrict.
  - transitivity (d[X; 2; fin_first⁺⁺⁺] (d[X; 3; fin_first⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺⁺] G.1).
      * apply func_proper. exact (F fin_first⁺
          ltac:(intros E; discriminate E)).
      * exact (snd (snd (snd G.2))).
  - transitivity (d[X; 2; fin_first⁺⁺⁺] (d[X; 3; fin_first⁺⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺⁺] (s[X; 2; fin_first⁺⁺] z.1)).
      * apply func_proper. exact (F fin_first⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (simplex_face_degeneracy_next (X := X)
          (fin_first⁺⁺ : Ordinal 2) z.1).
  - transitivity (d[X; 2; fin_first⁺⁺⁺] (d[X; 3; fin_first⁺⁺⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺⁺⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺⁺] H.1).
      * apply func_proper. exact (F fin_first⁺⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (snd (snd (snd H.2))).
Defined.

(** Read the backward composite without changing x or z. *)

(** 读出反向合成，不改变 x 或 z。 *)

Definition SphereCompositeSecondBackOfFiller
    {x y y' z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b y y') (H : TwoSphereComposite X b x y' z)
    (V : X 4) (HV : is_horn_filler (SphereSecondBackwardHornN X b G H) V)
  : TwoSphereComposite X b x y z.
Proof.
  assert (F : ∀ j (Hj : ¬ j = fin_first⁺⁺⁺),
    d[X; 3; j] V ≈S sphere_second_transport_faces X b z H.1 G.1 j).
  { intros j Hj. exact (sphere_second_transport_filler_face X b H G
      fin_first⁺⁺⁺ (λ R, match R eq_refl with end)
      (λ _, reflexivity y') V HV j Hj). }
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
    + transitivity (d[X; 2; fin_first⁺⁺] G.1).
      * apply func_proper. exact (F fin_first⁺
          ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd G.2))).
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] (s[X; 2; fin_first⁺⁺] z.1)).
      * apply func_proper. exact (F fin_first⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (simplex_face_degeneracy_id (X := X)
          (fin_first⁺⁺ : Ordinal 2) z.1).
  - transitivity (d[X; 2; fin_first⁺⁺⁺] (d[X; 3; fin_first⁺⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺⁺⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺⁺] H.1).
      * apply func_proper. exact (F fin_first⁺⁺⁺⁺
          ltac:(intros E; discriminate E)).
      * exact (snd (snd (snd H.2))).
Defined.

End GivenSecondTransport.

(** ** Choosing the Two Elementary Directions

    Fix the ambient simplicial setoid and vertex. Forward transport uses
    only missing-face-four selection; backward uses only missing-face-three
    selection. No respectfulness or uniqueness of the choices is assumed. *)

(** ** 选择两个初等方向

    固定环境单纯广集及顶点。正向仅使用缺第四面的选择，反向仅使用缺第三面的
    选择；不假设选择保相等或唯一。 *)

Section ChosenSecondTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Transport forward along the supplied elementary homotopy. *)

(** 沿给定初等同伦正向运输。 *)

Definition SphereCompositeSecondHomotopy
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    {x y y' z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b y y')
    (H : TwoSphereComposite X b x y z)
  : TwoSphereComposite X b x y' z.
Proof.
  pose (V := horn_fill (SphereSecondForwardHornN X b G H)).
  exact (SphereCompositeSecondOfFiller X b G H V.1 V.2).
Defined.

(** Transport back along the supplied elementary homotopy. *)

(** 沿给定初等同伦反向运输。 *)

Definition SphereCompositeSecondHomotopyBack
    `{HX : !HasHornFillers X 4 fin_first⁺⁺⁺}
    {x y y' z : TwoSphereS X b}
    (G : TwoSphereHomotopy X b y y')
    (H : TwoSphereComposite X b x y' z)
  : TwoSphereComposite X b x y z.
Proof.
  pose (V := horn_fill (SphereSecondBackwardHornN X b G H)).
  exact (SphereCompositeSecondBackOfFiller X b G H V.1 V.2).
Defined.

End ChosenSecondTransport.

(** ** Generated Second-Input Transport

    Fix only the two four-horn selections used by elementary transport.
    Fold the existing generated equality into Type-valued two-way
    implication of composite-witness types. The maps retain their full
    computational witnesses; no inverse laws on tetrahedra are asserted. *)

(** ** 第二输入的生成运输

    仅固定初等运输所需的两个四维 horn 选择。将既有生成相等折叠到合成见证类型
    的 Type 值双向蕴含，保留完整计算见证，不声称四面体上的互逆律。 *)

Section SecondClassTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.

(** Generated second-input equality preserves the same first input and
    output representative in both computational directions. *)

(** 第二输入的生成相等在两个计算方向均保留相同第一输入及输出代表。 *)

Definition two_sphere_composite_second_class
    {y y' : TwoSphereS X b} (E : (y : TwoSphereClassS X b) ≈S y')
    (x z : TwoSphereS X b)
  : TwoSphereComposite X b x y z ↔ TwoSphereComposite X b x y' z.
Proof.
  refine (@equiv_closure_preserves _ _ _ iffT _
    (λ a, TwoSphereComposite X b x a z) _ y y' E).
  - split; typeclasses eauto.
  - intros a a' [F | G].
    + split; intros H.
      * exact (TwoSphereCompositeChangeEndpoints X b H
          (reflexivity x) F (reflexivity z)).
      * exact (TwoSphereCompositeChangeEndpoints X b H
          (reflexivity x) (symmetry F) (reflexivity z)).
    + split; intros H.
      * exact (SphereCompositeSecondHomotopy X b G H).
      * exact (SphereCompositeSecondHomotopyBack X b G H).
Defined.

End SecondClassTransport.

(** ** A Respectful Map for Each Fixed First Input

    In addition to transport selections, fix missing-face-two four-horn
    selection for output comparison. The three-horn selections remain
    explicit data and may differ. This packages only a partial class map;
    simultaneous binary descent and group laws are subsequent work. *)

(** ** 每个固定第一输入的保相等映射

    在运输选择之外，固定缺第二面的四维 horn 选择用于输出比较。三维 horn
    选择仍为显式数据，且可以不同。此处仅打包偏类映射；同时二元下降及群律
    留待后续工作。 *)

Section SecondClassMap.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.

(** Independent three-horn choices preserve output classes along any
    generated second-input equality. *)

(** 独立的三维 horn 选择沿任意第二输入生成相等保持输出类。 *)

Lemma two_sphere_kan_composite_second_class_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    {y y' : TwoSphereS X b} (E : (y : TwoSphereClassS X b) ≈S y')
    (x : TwoSphereS X b)
  : ((@SphereKanComposite X b H x y).1 : TwoSphereClassS X b) ≈S
      (@SphereKanComposite X b K x y').1.
Proof.
  exact (two_sphere_composite_output_eq X b
    (fst (two_sphere_composite_second_class X b E x
      (@SphereKanComposite X b H x y).1)
      (@SphereKanComposite X b H x y).2)
    (@SphereKanComposite X b K x y').2).
Defined.

(** With the first representative fixed, the second input is a genuine
    respectful map on the existing sphere class setoid. *)

(** 固定第一代表后，第二输入给出既有球面类广集上的真正保相等映射。 *)

Program Definition two_sphere_kan_composite_second_resp
    (H : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereS X b)
  : TwoSphereClassS X b →r TwoSphereClassS X b
  :=
  {|func y := (@SphereKanComposite X b H x y).1
  |}.
Next Obligation.
  intros y y' E. exact (two_sphere_kan_composite_second_class_eq H H E x).
Defined.

(** Different selections give pointwise class-equal partial maps. *)

(** 不同选择给出逐点类相等的偏映射。 *)

Lemma two_sphere_kan_composite_second_choice_eq
    (H K : HasHornFillers X 3 fin_first⁺⁺) (x : TwoSphereS X b)
  : two_sphere_kan_composite_second_resp H x ≈f
      two_sphere_kan_composite_second_resp K x.
Proof.
  intros y. exact (two_sphere_kan_composite_choice_eq X b H K x y).
Defined.

End SecondClassMap.
