From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereKanComparison.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Moving a Sphere Homotopy from the First to the Last Faces

    A tetrahedron with faces (x,y,b₂,b₂) does not have the defining face
    table (b₂,b₂,x,y) of [TwoSphereHomotopy]. In particular, the first
    tetrahedron of a relative triangle cylinder has the former table.
    We must construct a comparison, rather than silently read it as a
    generator in [TwoSphereClassS].

    Prescribe faces 0, 2, 3 and 4 of a four-simplex V as s₂x, b₃, s₀x
    and the given tetrahedron w. All six intersections agree by their
    original specified simplex equality. The general
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}% supplies the actual horn. Its missing face d₁V
    has the required standard homotopy table. No triangle equality
    between x and y is assumed, and w need not equal d₁V.

    First retain a supplied filler and its equation. Then an explicit
    four-dimensional missing-face-one choice gives the conversion and
    hence generated class equality. No three-dimensional selection,
    multiplication, group, full Kan or filler uniqueness is needed.
    This is a prerequisite for general relative-cylinder comparison;
    it does not yet identify π₂ or provide arbitrary-path base change. *)

(** * 将球面同伦从最前两面移到最后两面

    面为 (x,y,b₂,b₂) 的四面体不具有 [TwoSphereHomotopy] 定义中的面表
    (b₂,b₂,x,y)。特别地，相对三角柱的第一块四面体具有前一种面表。
    因此必须构造比较，不能直接将它读成 [TwoSphereClassS] 的生成元。

    将四维单形 V 的第 0、2、3、4 面分别指定为 s₂x、b₃、s₀x 及给定
    四面体 w。六个交叠均按原有指定单形相等一致。通用的
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}% 给出实际 horn，其缺失面 d₁V 具有所需的标准同伦面表。
    不预设 x 与 y 的三角形相等，也不要求 w 与 d₁V 相等。

    先保留给定填充及其方程，再由显式四维缺第一面选择得到转换及生成类相等。
    不要求三维选择、乘法、群、完整 Kan 或填充唯一性。这是一般相对柱比较的
    前置，尚不识别 π₂ 或给出任意路径换基。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
w:(x,y,b_2,b_2) \arrow[r,"{d_4}",leftarrow] &
V \arrow[r,dashed,"{d_1}"] & h:(b_2,b_2,x,y)
\end{tikzcd}
\qquad $(d_0V,d_2V,d_3V)=(s_2x,b_3,s_0x).$
\end{center}%
*)

(** ** Supplied Tetrahedra and Degenerate Side Faces

    Fix independent simplex carrier/equality sizes and a base vertex.
    The low-face relation retains its tetrahedron and all four equations;
    it is not postulated to be an equivalence relation. *)

(** ** 给定四面体与退化侧面

    固定独立单形载体／相等大小及基点。低索引面关系保留四面体和全部四个方程，
    不预设它是等价关系。 *)

Section LowFaceWitnesses.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** A witness whose two possibly nonconstant faces are the first two. *)

(** 两个可非平凡面位于最前两面的见证。 *)

Definition TwoSphereLowHomotopy (x y : TwoSphereS X b)
  : Type
  := ∃ w : X 3,
      (d[X; 2; fin_first] w ≈S x.1) ∧
      (d[X; 2; fin_first⁺] w ≈S y.1) ∧
      (d[X; 2; fin_first⁺⁺] w ≈S simplex_constant X b 2) ∧
      (d[X; 2; fin_first⁺⁺⁺] w ≈S simplex_constant X b 2).

(** Endpoint replacement retains the original tetrahedron. *)

(** 端点替换保留原四面体。 *)

Definition TwoSphereLowHomotopyChangeEndpoints
    {x y x' y' : TwoSphereS X b} (H : TwoSphereLowHomotopy x y)
    (E : x ≈S x') (F : y ≈S y')
  : TwoSphereLowHomotopy x' y'.
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]]. exists w.
  split; [| split; [| split]].
  - transitivity x.1; assumption.
  - transitivity y.1; assumption.
  - exact H2.
  - exact H3.
Defined.

(** Both endpoints respect original sphere equality, without equating
    witnesses or enabling an equivalence structure. *)

(** 两端保持原球面相等，不等同见证或启用等价结构。 *)

Global Instance TwoSphereLowHomotopy_proper
  : Proper ([≈S] ==> [≈S] ==> iffT) TwoSphereLowHomotopy.
Proof.
  intros x x' E y y' F. split; intros H.
  - exact (TwoSphereLowHomotopyChangeEndpoints H E F).
  - exact (TwoSphereLowHomotopyChangeEndpoints H (symmetry E) (symmetry F)).
Defined.

(** The last two faces of the first degeneracy are constant. *)

(** 第一个退化的最后两面为常值。 *)

Lemma sphere_degenerate_first_high (x : TwoSphereS X b) (i : Ordinal 1)
  : d[X; 2; i⁺⁺] (s[X; 2; fin_first] x.1) ≈S
      simplex_constant X b 2.
Proof.
  transitivity (s[X; 1; fin_first] (d[X; 1; i⁺] x.1)).
  - exact (simplex_face_degeneracy_after (X := X)
      (i⁺ : Ordinal 2) (fin_first : Ordinal 1)
      ltac:(destruct i as [[] | [[] | []]]; cbn; repeat constructor) x.1).
  - transitivity (s[X; 1; fin_first] (simplex_constant X b 1)).
    + apply func_proper. exact (x.2 i⁺).
    + apply simplex_constant_restrict.
Defined.

(** Face one is a dummy and imposes no restriction on the filler. *)

(** 第一面为占位，不对填充施加约束。 *)

Definition sphere_low_homotopy_faces (x : TwoSphereS X b)
    (w : X 3) (j : Ordinal 4)
  : X 3
  := match fin_rank j with
  | 0 => s[X; 2; fin_first⁺⁺] x.1
  | 3 => s[X; 2; fin_first] x.1
  | 4 => w
  | _ => simplex_constant X b 3
  end.

(** Check six intersections, without using any equality of x and y. *)

(** 检查六个交叠，不使用 x 与 y 之间的相等。 *)

Lemma sphere_low_homotopy_faces_pairwise {x y : TwoSphereS X b}
    (H : TwoSphereLowHomotopy x y) (j k : Ordinal 4)
    (Hj : ¬ j = fin_first⁺) (Hk : ¬ k = fin_first⁺) (E : ¬ j = k)
  : d[X; 2; coface_intersection_index j k E]
      (sphere_low_homotopy_faces x H.1 j) ≈S
      d[X; 2; coface_intersection_index k j
        (λ F, E (symmetry F))] (sphere_low_homotopy_faces x H.1 k).
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]].
  assert (A02 : d[X; 2; fin_first⁺] (s[X; 2; fin_first⁺⁺] x.1) ≈S
    d[X; 2; fin_first] (simplex_constant X b 3)).
  { transitivity (simplex_constant X b 2).
    - exact (sphere_comparison_degenerate_low X b x fin_first⁺).
    - symmetry. apply simplex_constant_restrict. }
  assert (A03 : d[X; 2; fin_first⁺⁺] (s[X; 2; fin_first⁺⁺] x.1) ≈S
    d[X; 2; fin_first] (s[X; 2; fin_first] x.1)).
  { transitivity x.1.
    - exact (simplex_face_degeneracy_id (X := X)
        (fin_first⁺⁺ : Ordinal 2) x.1).
    - symmetry. exact (simplex_face_degeneracy_id (X := X)
        (fin_first : Ordinal 2) x.1). }
  assert (A04 : d[X; 2; fin_first⁺⁺⁺] (s[X; 2; fin_first⁺⁺] x.1) ≈S
    d[X; 2; fin_first] w).
  { transitivity x.1.
    - exact (simplex_face_degeneracy_next (X := X)
        (fin_first⁺⁺ : Ordinal 2) x.1).
    - symmetry. exact H0. }
  assert (A23 : d[X; 2; fin_first⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first⁺⁺] (s[X; 2; fin_first] x.1)).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact (sphere_degenerate_first_high x fin_first). }
  assert (A24 : d[X; 2; fin_first⁺⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first⁺⁺] w).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact H2. }
  assert (A34 : d[X; 2; fin_first⁺⁺⁺] (s[X; 2; fin_first] x.1) ≈S
    d[X; 2; fin_first⁺⁺⁺] w).
  { transitivity (simplex_constant X b 2).
    - exact (sphere_degenerate_first_high x fin_first⁺).
    - symmetry. exact H3. }
  destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]],
    k as [[] | [[] | [[] | [[] | [[] | []]]]]];
    try solve [destruct (Hj eq_refl) | destruct (Hk eq_refl) |
      destruct (E eq_refl)].
  all: first [exact A02 | exact A03 | exact A04 | exact A23 |
    exact A24 | exact A34 | exact (symmetry A02) | exact (symmetry A03) |
    exact (symmetry A04) | exact (symmetry A23) | exact (symmetry A24) |
    exact (symmetry A34)].
Defined.

(** Descend the retained faces to a genuine missing-face-one horn. *)

(** 将保留面下降为真正缺第一面的 horn。 *)

Definition SphereLowHomotopyHornN {x y : TwoSphereS X b}
    (H : TwoSphereLowHomotopy x y)
  : HornS X 4 fin_first⁺
  := HornFacesN X 2 fin_first⁺ (sphere_low_homotopy_faces x H.1)
      (sphere_low_homotopy_faces_pairwise H).

(** Recover each prescribed face from the full filler equation. *)

(** 从完整填充方程恢复每个给定面。 *)

Lemma sphere_low_homotopy_filler_face {x y : TwoSphereS X b}
    (H : TwoSphereLowHomotopy x y) (V : X 4)
    (HV : is_horn_filler (SphereLowHomotopyHornN H) V)
    (j : Ordinal 4) (Hj : ¬ j = fin_first⁺)
  : d[X; 3; j] V ≈S sphere_low_homotopy_faces x H.1 j.
Proof.
  transitivity (face[fin_first⁺; j; Hj] (SphereLowHomotopyHornN H)).
  - exact (fst (horn_filler_faces_iff _ V) HV j Hj).
  - apply horn_faces_β.
Defined.

(** Read the missing tetrahedron and its four standard homotopy equations.
    The input tetrahedron and the supplied filler remain independent. *)

(** 读出缺失四面体及其四个标准同伦方程；输入四面体与给定填充仍相互独立。 *)

Definition SphereLowHomotopyOfFiller {x y : TwoSphereS X b}
    (H : TwoSphereLowHomotopy x y) (V : X 4)
    (HV : is_horn_filler (SphereLowHomotopyHornN H) V)
  : TwoSphereHomotopy X b x y.
Proof.
  exists (d[X; 3; fin_first⁺] V). split; [| split; [| split]].
  - transitivity (d[X; 2; fin_first] (d[X; 3; fin_first] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first : Ordinal 3) fin_first ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first] (s[X; 2; fin_first⁺⁺] x.1)).
      * apply func_proper. exact (sphere_low_homotopy_filler_face H V HV
          fin_first ltac:(intros E; discriminate E)).
      * exact (sphere_comparison_degenerate_low X b x fin_first).
  - transitivity (d[X; 2; fin_first⁺] (d[X; 3; fin_first⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺] (simplex_constant X b 3)).
      * apply func_proper. exact (sphere_low_homotopy_filler_face H V HV
          fin_first⁺⁺ ltac:(intros E; discriminate E)).
      * apply simplex_constant_restrict.
  - transitivity (d[X; 2; fin_first⁺] (d[X; 3; fin_first⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺] (s[X; 2; fin_first] x.1)).
      * apply func_proper. exact (sphere_low_homotopy_filler_face H V HV
          fin_first⁺⁺⁺ ltac:(intros E; discriminate E)).
      * exact (simplex_face_degeneracy_next (X := X)
          (fin_first : Ordinal 2) x.1).
  - transitivity (d[X; 2; fin_first⁺] (d[X; 3; fin_first⁺⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺] H.1).
      * apply func_proper. exact (sphere_low_homotopy_filler_face H V HV
          fin_first⁺⁺⁺⁺ ltac:(intros E; discriminate E)).
      * exact (fst (snd H.2)).
Defined.

End LowFaceWitnesses.

(** ** Selecting Only the Required Four-Horn

    Fix the same independent sizes and base vertex, choosing only
    missing-face-one fillers in dimension four. Retain the converted
    elementary witness before inserting it into generated class equality. *)

(** ** 仅选择所需四维 Horn

    固定同样的独立大小及基点，仅选择四维缺第一面的填充。先保留转换后的
    初等见证，再将它放入生成类相等。 *)

Section ChosenLowHomotopy.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX1 : !HasHornFillers X 4 fin_first⁺}.

(** Select the comparison filler, without equating it with the input. *)

(** 选择比较填充，不将其与输入等同。 *)

Definition SphereLowHomotopy {x y : TwoSphereS X b}
    (H : TwoSphereLowHomotopy X b x y)
  : TwoSphereHomotopy X b x y.
Proof.
  pose (V := horn_fill (SphereLowHomotopyHornN X b H)).
  exact (SphereLowHomotopyOfFiller X b H V.1 V.2).
Defined.

(** The converted actual tetrahedron supplies a standard class generator. *)

(** 转换后的实际四面体给出标准类生成元。 *)

Lemma two_sphere_low_homotopy_class {x y : TwoSphereS X b}
    (H : TwoSphereLowHomotopy X b x y)
  : (x : TwoSphereClassS X b) ≈S y.
Proof. exact (two_sphere_class_step X b (SphereLowHomotopy H)). Defined.

End ChosenLowHomotopy.
