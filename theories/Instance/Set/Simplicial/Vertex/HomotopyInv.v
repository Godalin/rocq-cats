From Cats Require Export
  Instance.Set.Simplicial.Vertex.Homotopy
  Instance.Set.Simplicial.Vertex.Reconstruction.
From Cats Require Import
  Instance.Set.Simplicial.Vertex.Product
  Instance.Set.Simplicial.Vertex.Ordinal
  Cat.Diagram.PrismReconstruction
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural.

Local Open Scope nat_scope.

(* begin hide *)

(** Introduce obligation variables without expanding the complete recovered
    cylinder. The proofs below explicitly use its named boundary laws. *)

(** 引入义务变量时不展开整个恢复出的柱；下列证明显式使用具名的边界定律。 *)

Local Obligation Tactic := intros.

(* end hide *)

(** * Recovering Natural Transformations from Nerve Homotopies

    A homotopy between vertex nerve maps has two kinds of data: a map on
    the whole simplicial cylinder and equations at its endpoints. Reconstruct
    a categorical prism from the map, then align its boundary labels using
    these equations. The time edge becomes a natural transformation with
    the original, fixed endpoint functors. *)

(** * 从 nerve 同伦恢复自然变换

    顶点 nerve 映射之间的同伦有两类数据：整个单纯柱上的映射，以及端点方程。
    先由映射重构范畴棱柱，再用端点方程对齐边界标签。时间边由此成为以原来
    两个固定函子为端点的自然变换。 *)

(** The product comparison
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.VertexNerveProductN}
    {%[VertexNerveProductN]%}% and the ordinal comparison
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Ordinal.OrdinalVertexNerveN}
    {%[OrdinalVertexNerveN]%}% turn the cylinder map into a map between nerves.
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Reconstruction.VertexNerveInvF}
    {%[VertexNerveInvF]%}% then recovers a functor K on the product with [1].
    Its boundary labels need only equal the requested labels in the specified
    setoid equality. Write their transport witnesses as p and q. The square
    below explains the correction: its top arrow is the recovered component,
    obtained by following the other three sides using the inverse of q's
    transport. Only the vertical transports must be invertible. *)

(** 积比较
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.VertexNerveProductN}
    {%[VertexNerveProductN]%}% 与序数比较
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Ordinal.OrdinalVertexNerveN}
    {%[OrdinalVertexNerveN]%}% 把柱映射变成 nerve 之间的映射，再由
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Reconstruction.VertexNerveInvF}
    {%[VertexNerveInvF]%}% 恢复与 [1] 的积上的函子 K。其边界标签只须按指定广集
    相等对应于所需标签。将相应的运输见证记为 p、q，下图解释如何校正：上边是
    恢复的分量，沿另外三边并使用 q 的运输的逆就能得到它。只有竖直运输需要
    可逆。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
F x \arrow[r,"{\eta_x}"] \arrow[d,"{U[p_x]}"'] &
G x \arrow[d,"{U[q_x]}"] \\
K(x,0) \arrow[r,"{K(\mathrm{id}_x,\delta)}"'] & K(x,1)
\end{tikzcd}
\end{center}%
*)

(** Here %$\delta:0\to1$% is the ordinal time step. Naturality of the
    corrected components follows from the whole prism and its boundary
    equations, not from independently choosing a path for each vertex. The
    general comparison
    %\coqref{Cats.Cat.Diagram.PrismReconstruction.PrismComparisonN}
    {%[PrismComparisonN]%}% proves the cylinder round trip after alignment. *)

(** 此处 %$\delta:0\to1$% 是序数时间步。校正后分量的自然性来自整个棱柱及其
    边界方程，无需为每个顶点独立选取路径。对齐后，使用通用比较
    %\coqref{Cats.Cat.Diagram.PrismReconstruction.PrismComparisonN}
    {%[PrismComparisonN]%}% 证明柱的往返律。 *)

(** ** From a Product Nerve to the Simplicial Cylinder

    Fix a presentation [T] and independent value sizes. Split a diagram in
    its product with the ordinal interval, then forget the interval's
    redundant vertex wrapper. This uses the existing product and ordinal
    nerve comparisons. *)

(** ** 从积的 nerve 到单纯柱

    固定呈现 [T] 及独立的值大小。拆分它与序数区间之积中的图式，再忘却区间
    冗余的顶点包装。此处复用已有的积与序数 nerve 比较。 *)

Section CylinderComparison.
Universes u p.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C).

(** Split the two coordinates and identify the ordinal nerve with [Δ[1]]. *)

(** 拆分两个坐标，并将序数的 nerve 与 [Δ[1]] 对应。 *)

Definition VertexNerveCylinderN
  : (Nᵥ(VertexProductObjF T (OrdinalObjF 1)) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ SimplicialCylinderF Nᵥ(T)
  := @PointwiseProductN _ _ SetCat_HasProduct _ _ _ _
      idN (OrdinalVertexNerveN 1) ∘Nv
      VertexNerveProductN T (OrdinalObjF 1).

(** Repackage the ordinary product category with its original labels. *)

(** 用原标签重新包装普通积范畴。 *)

Definition VertexIntervalProductF
  : Fct (VertexCat T ×C [Ord 1])
      (VertexCat (VertexProductObjF T (OrdinalObjF 1)))
  := InducedProductInvF X (FinS@{Set Set Set} 2) T (OrdinalObjF 1)
      ∘F (IdF ×F OrdinalVertexInvF 1).

End CylinderComparison.

(** ** Reconstructing and Aligning the Prism

    Fix presentations [T], [U], functors [F], [G], and a homotopy [H]
    between their nerve maps. Full faithfulness reconstructs the cylinder
    map on the product presentation. The endpoint equations then supply
    specified equalities from [F x] and [G x] to the reconstructed labels. *)

(** ** 重构并对齐棱柱

    固定呈现 [T]、[U]，函子 [F]、[G] 及其 nerve 映射之间的同伦 [H]。
    全忠实性在积呈现上重构柱映射；端点方程随后提供从 [F x]、[G x] 到重构
    标签的指定相等。 *)

Section Reconstruction.
Universes u p.
Context {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U}
    (H : SimplicialHomotopy
      (VertexNerveN F :
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
      (VertexNerveN G)).

(** View the cylinder map as a map out of the product presentation's nerve. *)

(** 将柱映射看作从积呈现的 nerve 出发的映射。 *)

Definition nerve_homotopy_product_map
  : (Nᵥ(VertexProductObjF T (OrdinalObjF 1)) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U)
  := homotopy_map H ∘Nv VertexNerveCylinderN T.

(** Recover the ordinary categorical prism by the existing nerve inverse. *)

(** 通过已有 nerve 逆构造恢复普通范畴棱柱。 *)

Definition NerveHomotopyPrismF
  : Fct (VertexCat T ×C [Ord 1]) (VertexCat U)
  := VertexNerveInvF nerve_homotopy_product_map ∘F VertexIntervalProductF T.

(** Restricting the recovered prism gives the original cylinder map in
    every degree, using specified labelled-diagram equality. *)

(** 在每个维度限制恢复的棱柱，按指定带标签图式相等得到原柱映射。 *)

Lemma nerve_homotopy_prism_β {n : nat}
    (P : Fct [Ord n] (VertexCat T)) (θ : Fct [Ord n] [Ord 1])
  : VertexDiagramEq U (NerveHomotopyPrismF ∘F PairF P θ)
      (lower (homotopy_map H n (⟨P⟩ᵥ, {|lower := θ|}))).
Proof.
  pose (Q := VertexIntervalProductF T ∘F PairF P θ).
  transitivity (lower (nerve_homotopy_product_map n ⟨Q⟩ᵥ)).
  - exact (lower (vertex_nerve_β nerve_homotopy_product_map n ⟨Q⟩ᵥ)).
  - apply (λ e, lower e).
    apply (@func_proper _ _ (homotopy_map H n)).
    split.
    + refine {|lower := _
              |}.
      exists (λ i, reflexivity (P i : X)). intros i j a.
      change (T⟦reflexivity (P j : X)⟧Ob ∘ fmap P a ≈
        fmap P a ∘ T⟦reflexivity (P i : X)⟧Ob).
      rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
    + refine {|lower := _
              |}.
      apply (snd (simplex_eq_iff _ _)). intros i. reflexivity.
Defined.

(** At constant time, the original endpoint equation identifies the
    reconstructed boundary with the chosen endpoint functor on any diagram. *)

(** 在常值时间，原端点方程把重构边界与选定端点函子在任意图式上的作用对应。 *)

Definition nerve_homotopy_boundary {n : nat}
    (P : Fct [Ord n] (VertexCat T)) (b : bool)
  : VertexDiagramEq U
      (NerveHomotopyPrismF ∘F
        PairF P (ConstF [Ord n] (C := [Ord 1])
          (simplex_interval_position b)))
      ((if b then G else F) ∘F P).
Proof.
  transitivity (lower (homotopy_map H n (⟨P⟩ᵥ,
    {|lower := ConstF [Ord n] (C := [Ord 1])
      (simplex_interval_position b)|}))).
  - apply nerve_homotopy_prism_β.
  - destruct b; exact (lower (homotopy_endpoint H _ n ⟨P⟩ᵥ)).
Defined.

(** The boundary label is chosen by the time position, without identifying
    distinct source or target objects by native equality. *)

(** 时间位置选取边界标签，不使用原生相等识别不同的源或目标对象。 *)

Definition nerve_homotopy_label (z : @Ob (VertexCat T ×C [Ord 1]))
  : Y
  := if ordinal_interval_side (snd z) then G (fst z) else F (fst z).

(** The endpoint comparisons supply exactly the transport for relabelling. *)

(** 端点比较恰提供重标记所需的运输。 *)

Definition nerve_homotopy_label_eq (z : @Ob (VertexCat T ×C [Ord 1]))
  : nerve_homotopy_label z ≈S NerveHomotopyPrismF z.
Proof.
  destruct z as [x [[] | [[] | []]]].
  - symmetry. exact ((nerve_homotopy_boundary
      (ConstF [Ord 0] (C := VertexCat T) x) false).1 fin_first).
  - symmetry. exact ((nerve_homotopy_boundary
      (ConstF [Ord 0] (C := VertexCat T) x) true).1 fin_first).
Defined.

(** Relabel by the specified endpoint transports, retaining the full prism. *)

(** 沿指定端点运输重标记，保留整个棱柱。 *)

Definition NerveHomotopyAlignedF
  : Fct (VertexCat T ×C [Ord 1]) (VertexCat U)
  := VertexRelabelF U NerveHomotopyPrismF
      nerve_homotopy_label nerve_homotopy_label_eq.

(** Endpoint equations identify arrows after any parallel specified endpoint
    transports. The edge simplex supplies the square, and witness independence
    makes its particular endpoint proof immaterial. *)

(** 端点方程在任意平行的指定端点运输之后识别箭头。一维单形提供交换方块，
    见证无关性保证不依赖其中具体的端点证明。 *)

Lemma nerve_homotopy_boundary_arrow (t : bool) {x y : X}
    (f : (@Hom (VertexCat T)) x y)
    (a : ((if t then (G : Fct (VertexCat T) (VertexCat U)) else F) x : Y) ≈S
      NerveHomotopyPrismF (x, simplex_interval_position t))
    (b : ((if t then (G : Fct (VertexCat T) (VertexCat U)) else F) y : Y) ≈S
      NerveHomotopyPrismF (y, simplex_interval_position t))
  : U⟦a; fmap NerveHomotopyPrismF
      (X := (x, simplex_interval_position t))
      (Y := (y, simplex_interval_position t)) (f, id); b⟧Ar ≈
      fmap (if t then G else F) f.
Proof.
  pose (e := △₁[T; x; y] f :
    (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 1).
  pose (E := nerve_homotopy_boundary (lower e) t).
  transitivity (U⟦a; fmap NerveHomotopyPrismF
    (X := (x, simplex_interval_position t))
    (Y := (y, simplex_interval_position t))
    (fmap (lower e) (ordinal_step fin_first), id); b⟧Ar).
  - apply func_proper. apply functor_fmap_proper. split.
    + symmetry. apply edge_simplex_arrow.
    + exact tt.
  - transitivity (U⟦reflexivity
      ((if t then (G : Fct (VertexCat T) (VertexCat U)) else F) x : Y);
      fmap (if t then G else F)
        (fmap (lower e) (ordinal_step fin_first));
      reflexivity
        ((if t then (G : Fct (VertexCat T) (VertexCat U)) else F) y : Y)⟧Ar).
    + exact (vertex_rebase_eq U a b _ _ (E.1 fin_first)
        (E.1 (fin_next fin_first)) _ _ (E.2 _ _ (ordinal_step fin_first))).
    + etransitivity; [apply vertex_rebase_id |].
      apply functor_fmap_proper. apply edge_simplex_arrow.
Defined.

(** The aligned boundary arrows are the original functor arrows. Its
    boundary object maps already compute to those of [F] and [G]. *)

(** 对齐后的边界箭头是原函子的箭头；其边界对象映射已计算为 [F]、[G] 的映射。 *)

Lemma nerve_homotopy_aligned_0 {x y : X}
    (f : (@Hom (VertexCat T)) x y)
  : fmap (π1F NerveHomotopyAlignedF fin_first) f ≈ fmap F f.
Proof.
  exact (nerve_homotopy_boundary_arrow false f
    (nerve_homotopy_label_eq (x, fin_first))
    (nerve_homotopy_label_eq (y, fin_first))).
Defined.

(** The final aligned boundary has the arrow map of [G]. *)

(** 对齐后的终止边界具有 [G] 的箭头映射。 *)

Lemma nerve_homotopy_aligned_1 {x y : X}
    (f : (@Hom (VertexCat T)) x y)
  : fmap (π1F NerveHomotopyAlignedF (fin_next fin_first)) f ≈ fmap G f.
Proof.
  exact (nerve_homotopy_boundary_arrow true f
    (nerve_homotopy_label_eq (x, fin_next fin_first))
    (nerve_homotopy_label_eq (y, fin_next fin_first))).
Defined.

(** Read the aligned prism's time edge, reusing general prism extraction.
    Boundary arrow equations give naturality for the original [F] and [G]. *)

(** 复用通用棱柱提取，读出对齐后的时间边。边界箭头方程给出对原 [F]、[G]
    的自然性。 *)

Program Definition VertexNerveInvHomotopyN
  : F ⇒ G
  :=
  {|nt x := PrismTransformationN NerveHomotopyAlignedF x
  |}.
Next Obligation.
  pose (E := nt_naturality (PrismTransformationN NerveHomotopyAlignedF) f).
  rewrite (nerve_homotopy_aligned_0 f), (nerve_homotopy_aligned_1 f) in E.
  exact E.
Defined.

(** Identity components compare the original endpoints to the aligned
    boundary functors; their arrow maps agree by the boundary equation. *)

(** 恒等分量将原端点与对齐后的边界函子比较，箭头映射由边界方程对应。 *)

Program Definition NerveHomotopyBoundaryN (b : bool)
  : (if b then G else F) ⇒
      π1F NerveHomotopyAlignedF (simplex_interval_position b)
  :=
  {|nt x := _
  |}.
Next Obligation. destruct b; exact id. Defined.
Next Obligation.
  destruct b.
  - change (id ∘ fmap G f ≈
      fmap (π1F NerveHomotopyAlignedF (simplex_interval_position true)) f ∘ id).
    rewrite comp_id_l, comp_id_r. symmetry.
    exact (nerve_homotopy_aligned_1 f).
  - change (id ∘ fmap F f ≈
      fmap (π1F NerveHomotopyAlignedF (simplex_interval_position false)) f ∘ id).
    rewrite comp_id_l, comp_id_r. symmetry.
    exact (nerve_homotopy_aligned_0 f).
Defined.

(** The recovered transformation and the two identity boundary comparisons
    form the square required by the general prism extension. *)

(** 恢复的自然变换与两个恒等边界比较组成通用棱柱延拓所需的交换方形。 *)

Lemma nerve_homotopy_boundary_square
  : (NerveHomotopyBoundaryN true ∘Nv VertexNerveInvHomotopyN) ≈N
      (PrismTransformationN NerveHomotopyAlignedF ∘Nv
        NerveHomotopyBoundaryN false).
Proof.
  intros x.
  change (id ∘ PrismTransformationN NerveHomotopyAlignedF x ≈
    PrismTransformationN NerveHomotopyAlignedF x ∘ id).
  rewrite comp_id_l, comp_id_r. reflexivity.
Defined.

(** Reuse the unique prescribed-boundary comparison of categorical prisms. *)

(** 复用指定边界的唯一范畴棱柱比较。 *)

Definition NerveHomotopyComparisonN
  : NaturalPrismF VertexNerveInvHomotopyN ⇒ NerveHomotopyAlignedF
  := PrismComparisonN NerveHomotopyAlignedF VertexNerveInvHomotopyN
      (NerveHomotopyBoundaryN false) (NerveHomotopyBoundaryN true)
      nerve_homotopy_boundary_square.

(** The generic comparison is a specified vertex comparison: its components
    are identities at both time positions, hence reflexive transports. *)

(** 通用比较是指定顶点比较：两个时间位置上的分量都是恒等，即自反运输。 *)

Definition nerve_homotopy_comparison
  : VertexDiagramEq U (NaturalPrismF VertexNerveInvHomotopyN)
      NerveHomotopyAlignedF.
Proof.
  assert (e : ∀ z, (NaturalPrismF VertexNerveInvHomotopyN z : Y) ≈S
    NerveHomotopyAlignedF z).
  { intros [x [[] | [[] | []]]]; reflexivity. }
  apply (vertex_diagram_comparison U e NerveHomotopyComparisonN).
  intros [x [[] | [[] | []]]]; rewrite vertex_transport_id; apply comp_id_l.
Defined.

(** Rebuilding after extraction recovers the entire cylinder map. This
    compares every simplex and time simplex, not just the vertex time edges. *)

(** 提取后重建恢复整个柱映射：比较每个单形与时间单形，而非仅比较顶点时间边。 *)

Lemma vertex_nerve_homotopy_β
  : HomotopyEq (VertexNerveHomotopy VertexNerveInvHomotopyN) H.
Proof.
  intros n [[P] [θ]]. refine {|lower := _
                             |}.
  transitivity (NerveHomotopyAlignedF ∘F PairF P θ).
  - exact (@func_proper _ _ (vertex_diagram_precomp_resp U (PairF P θ))
      _ _ nerve_homotopy_comparison).
  - transitivity (NerveHomotopyPrismF ∘F PairF P θ).
    + exact (@func_proper _ _ (vertex_diagram_precomp_resp U (PairF P θ))
        _ _ (vertex_relabel_eq U NerveHomotopyPrismF
          nerve_homotopy_label nerve_homotopy_label_eq)).
    + apply nerve_homotopy_prism_β.
Defined.

End Reconstruction.

(** The forward bridge detects equality of transformations. Evaluate it on
    a constant source edge and the generic time edge; its arrow is exactly
    the transformation component, with fixed endpoint labels. *)

(** 前向桥梁检测自然变换的相等：在常值源边及泛时间边上求值，其箭头恰为
    自然变换分量，端点标签固定。 *)

Lemma vertex_nerve_homotopy_faithful@{u p +}
    {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (α β : F ⇒ G)
    (E : HomotopyEq
      (VertexNerveHomotopy α : SimplicialHomotopy
        (VertexNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
        (VertexNerveN G)) (VertexNerveHomotopy β))
  : α ≈N β.
Proof.
  intros x.
  pose (z := (⟨ConstF [Ord 1] (C := VertexCat T) x⟩ᵥ, simplex_generic 1)).
  pose proof (vertex_edge_square
    (VertexNerveHomotopyN α 1 z) (VertexNerveHomotopyN β 1 z)
    (reflexivity (F x : Y)) (reflexivity (G x : Y)) (E 1 z)) as S.
  change (U⟦reflexivity (G x : Y)⟧Ob ∘
    fmap (NaturalPrismF α)
      (X := (x, fin_first)) (Y := (x, fin_next fin_first))
      (id, ordinal_step fin_first) ≈
    fmap (NaturalPrismF β)
      (X := (x, fin_first)) (Y := (x, fin_next fin_first))
      (id, ordinal_step fin_first) ∘ U⟦reflexivity (F x : Y)⟧Ob) in S.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r in S.
  transitivity (fmap (NaturalPrismF α)
    (X := (x, fin_first)) (Y := (x, fin_next fin_first))
    (id, ordinal_step fin_first)).
  - symmetry. apply natural_prism_step.
  - etransitivity; [exact S | apply natural_prism_step].
Defined.

(** Extracting the forward homotopy returns the original transformation,
    in pointwise hom equality. The cylinder round trip and faithfulness
    avoid any equality between endpoint-equation proof fields. *)

(** 提取前向同伦按逐点 Hom 相等返回原自然变换。使用柱的往返律及忠实性，
    无需比较端点方程的证明字段。 *)

Lemma vertex_nerve_homotopy_η@{u p +}
    {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (α : F ⇒ G)
  : VertexNerveInvHomotopyN
      (VertexNerveHomotopy α : SimplicialHomotopy
        (VertexNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
        (VertexNerveN G)) ≈N α.
Proof.
  apply vertex_nerve_homotopy_faithful.
  apply vertex_nerve_homotopy_β.
Defined.

(** Both composites recover their input in its specified equality:
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.HomotopyInv.vertex nerve homotopy xCExB7}
    {%[vertex_nerve_homotopy_η]%}% uses pointwise hom equality, while
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.HomotopyInv.vertex nerve homotopy xCExB2}
    {%[vertex_nerve_homotopy_β]%}% compares the entire cylinder maps. Thus this
    correspondence retains directed, possibly noninvertible transformations. *)

(** 两个复合都按各自的指定相等恢复输入：
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.HomotopyInv.vertex nerve homotopy xCExB7}
    {%[vertex_nerve_homotopy_η]%}% 使用逐点 Hom 相等，
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.HomotopyInv.vertex nerve homotopy xCExB2}
    {%[vertex_nerve_homotopy_β]%}% 比较整个柱映射。因此，此对应保留有向且可能
    不可逆的自然变换。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge]
\operatorname{Nat}(F,G)
  \arrow[r,bend left=18,"{N_{\mathrm v}}"] &
\operatorname{Homot}_{\Delta}(N_{\mathrm v}F,N_{\mathrm v}G)
  \arrow[l,bend left=18,"{\mathrm{recover}}"]
\end{tikzcd}
\end{center}%
*)

(** Equal homotopies recover equal transformations. Only the stored cylinder
    maps are compared, so endpoint witnesses may differ. *)

(** 相等同伦恢复相等自然变换；只比较所存柱映射，端点见证可以不同。 *)

Global Instance vertex_nerve_inv_homotopy_proper@{u p +}
    {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U}
  : Proper (HomotopyEq ==> NatEq)
      (@VertexNerveInvHomotopyN _ _ _ _ T U F G :
        SimplicialHomotopy
          (VertexNerveN F :
            (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
          (VertexNerveN G) → _).
Proof.
  intros H K E. apply vertex_nerve_homotopy_faithful.
  transitivity H; [apply vertex_nerve_homotopy_β |].
  transitivity K; [exact E |].
  symmetry. apply vertex_nerve_homotopy_β.
Defined.
