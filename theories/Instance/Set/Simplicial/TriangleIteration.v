From Cats Require Export
  Instance.Set.Simplicial.TriangleAttachment
  Cat.Extension.Chain.
From Cats Require Import
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Nine Actual Extensions to the Triangle Product

    The existing [TriangleHornStageInclusionN] arrows form the existing
    [Chain]. Each edge extension comes from [TriangleHornStepExtension],
    and [chain_extension_target] performs the finite iteration. The final
    stage recovers the whole product through [TriangleHornFinalN].

    The input is an actual map on the complete initial region: spatial
    boundary times parameter triangle, union spatial triangle times the
    specified parameter horn. Its recovery holds at every source degree.
    Only the nine listed three- and four-dimensional horn choices are
    used. Neither full Kan nor choice Proper/uniqueness is required.

    This constructs the extension from given initial-region data.
    %\coqref{Cats.Instance.Set.Simplicial.TriangleInput.TriangleInputN}
    {%[TriangleInputN]%}% now glues boundary and retained time-edge maps
    with explicit common-factor agreement.
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereTriangleInput.SphereCompositeTriangleInput}
    {%[SphereCompositeTriangleInput]%}% supplies this initial map directly
    from two actual composable relative cylinders and their endpoint laws. *)

(** * 九次实际延拓到三角积

    既有 [TriangleHornStageInclusionN] 箭头组成既有 [Chain]。每条边的延拓
    来自 [TriangleHornStepExtension]，由 [chain_extension_target] 进行有限
    迭代，再通过 [TriangleHornFinalN] 从最终阶段恢复完整积。

    输入是完整初始区域上的实际映射：空间边界乘参数三角形，并上空间三角形乘
    指定参数 horn。恢复方程对每个来源维数成立。只使用列出的九份三维和四维
    horn 选择，不要求完整 Kan 或选择 Proper/唯一。

    本章从给定初始区域数据构造延拓。
    %\coqref{Cats.Instance.Set.Simplicial.TriangleInput.TriangleInputN}
    {%[TriangleInputN]%}% 现以显式共同因子相容粘合边界及保留时间边映射。
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereTriangleInput.SphereCompositeTriangleInput}
    {%[SphereCompositeTriangleInput]%}% 从两个实际可复合相对柱及其端点律直接
    给出这一初始映射。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
A_0 \arrow[r] \arrow[ddr,"a"'] & A_1 \arrow[r] & \cdots
  \arrow[r] & A_9 \arrow[d,"\cong"] \\
&&& \Delta[2]\times\Delta[2] \arrow[dll,dashed,"b"] \\
& X
\end{tikzcd}
\qquad $b|_{A_0}\approx a.$
\end{center}%
*)

(** ** The Given Stage Geometry

    Fix independent value/equality bounds and a missing parameter face.
    No target or filler choices are used to build the chain and its
    coordinate-preserving comparison with the ambient product. *)

(** ** 给定阶段几何

    固定独立取值/相等界及参数缺面。链及其保留坐标的环境积比较不使用目标或
    填充选择。 *)

Section Iteration.
Universes u p.
Context (r : Ordinal 2).

(** Ten actual stages and the nine original adjacent inclusions.
    Finite case analysis keeps the original maps transparent, avoiding
    transports along opaque native rank-equality proofs. *)

(** 十个实际阶段及九条原相邻包含。有限分类保持原映射透明，避免沿不透明原生
    编号相等证明运输。 *)

Program Definition TriangleHornChain
  : Chain (FctCat (Δ^op) SetCat@{u p _ _ _ _ _}) 9
  :=
  {|chain_vertex i :=
      TriangleHornStage@{u p _ _ _ _ _ _ _ _ _ _ _ _} r (fin_rank i)
  ; chain_edge s := _
  |}.
Next Obligation.
  destruct s as [[] | [[] | [[] | [[] |
      [[] | [[] | [[] | [[] | [[] | []]]]]]]]]].
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺ : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺⁺ : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺⁺⁺ : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺⁺⁺⁺ : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺⁺⁺⁺⁺ : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺⁺⁺⁺⁺⁺ : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8)).
  - exact (TriangleHornStageInclusionN@{u p _ _ _ p _ _ _ _ _ u _ _} r
      (fin_first⁺⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8)).
Defined.

Let c
  : Chain (FctCat (Δ^op) SetCat@{u p _ _ _ _ _}) 9
  := TriangleHornChain.

Let chain_inclusions
  : ⟦c⟧Ch ⇒
      ConstF (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _}) [Ord 9]
      (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Proof.
  refine (ChainCompareN c
    (ConstF (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _}) [Ord 9]
      TriangleHornAmbient)
    (λ i, RegionInclusionN (TriangleHornRegion r (fin_rank i))) _).
  intros s. destruct s as [[] | [[] | [[] | [[] |
      [[] | [[] | [[] | [[] | [[] | []]]]]]]]]];
    intros n [x H]; change (x ≈S x); reflexivity.
Defined.

(** Every interpreted interval preserves both ambient coordinates.
    Naturality of the existing chain comparison proves this without
    expanding a nine-fold composite or equating membership witnesses. *)

(** 每个解释区间保留两个环境坐标。已有链比较的自然性证明此事，无需展开九重
    复合或等同隶属见证。 *)

Definition triangle_horn_chain_segment_comm (i j : Ordinal 9)
    (f : (@Hom [Ord 9]) i j)
  : (RegionInclusionN (TriangleHornRegion r (fin_rank j)) ∘Nv
      chain_segment c i j f) ≈N
      RegionInclusionN (TriangleHornRegion r (fin_rank i)).
Proof.
  transitivity (idN ∘Nv
    RegionInclusionN (TriangleHornRegion r (fin_rank i))).
  - exact (nt_naturality chain_inclusions f).
  - intros n x. reflexivity.
Defined.

Let last
  : Ordinal 9
  := fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺.

Let total_segment
  : TriangleHornStage r 0 ⇒
      (TriangleHornStage r 9 : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := chain_segment c fin_first last
      (ordinal_from_first last).

(** The inverse final-stage comparison restricts to the same interval
    map in specified equality. It need not recover membership records. *)

(** 最终阶段比较的逆限制后，按指定相等得到同一区间映射，无需恢复隶属记录。 *)

Definition triangle_horn_initial_segment
  : (TriangleHornFinalN r ∘Nv
      RegionInclusionN (TriangleHornRegion r 0)) ≈N total_segment.
Proof.
  apply (region_inclusion_mono (TriangleHornRegion r 9)).
  transitivity (RegionInclusionN (TriangleHornRegion r 0)).
  - intros n x. change (x.1 ≈S x.1). reflexivity.
  - symmetry. exact (triangle_horn_chain_segment_comm
      fin_first last (ordinal_from_first last)).
Defined.

(** ** Explicit Step Choices and Recovery

    Fix a target and only the dimension/missing-face choice occurring at
    each actual step. These choices are arbitrary functions; no equations
    between them or respectfulness of selecting them are assumed. *)

(** ** 显式步骤选择及恢复

    固定目标，只为每个实际步骤给定对应维数/缺面的选择。这些选择是任意函数，
    不假设它们之间的方程或选择操作保相等。 *)

Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing r s)).

(** Each edge uses exactly its original single-step extension operation.
    Naming this family keeps later iteration abstract during checking;
    the actual supplied maps and recovery equations remain transparent. *)

(** 每条边恰好使用原单步延拓操作。命名此族使后续迭代在检查时保持抽象；
    实际给定映射及恢复方程仍透明。 *)

Local Opaque TriangleHornStepExtension.

Definition triangle_horn_edge_extensions (s : Fin@{Set} 9)
  : is_extension_target (chain_edge c s) X.
Proof.
  destruct s as [[] | [[] | [[] | [[] |
      [[] | [[] | [[] | [[] | [[] | []]]]]]]]]].
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first : Ordinal 8)
      (K (fin_first)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺ : Ordinal 8)
      (K (fin_first⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺⁺ : Ordinal 8)
      (K (fin_first⁺⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺⁺⁺ : Ordinal 8)
      (K (fin_first⁺⁺⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺⁺⁺⁺ : Ordinal 8)
      (K (fin_first⁺⁺⁺⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺⁺⁺⁺⁺ : Ordinal 8)
      (K (fin_first⁺⁺⁺⁺⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺⁺⁺⁺⁺⁺ : Ordinal 8)
      (K (fin_first⁺⁺⁺⁺⁺⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8)
      (K (fin_first⁺⁺⁺⁺⁺⁺⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
  - intros a.
    pose (e := TriangleHornStepExtension r (fin_first⁺⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8)
      (K (fin_first⁺⁺⁺⁺⁺⁺⁺⁺)) a).
    exists e.1. intros n x. exact (fst e.2 n x).
Defined.

Local Opaque chain_extension_target.

(** The integrated general finite-chain extension constructs the final
    stage map, keeping its original interval restriction equation. *)

(** 已集成的一般有限链延拓构造最终阶段映射，保留原区间限制方程。 *)

Definition triangle_horn_chain_extension_target
  : is_extension_target (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
      total_segment X.
Proof.
  intros a.
  refine (@chain_extension_target (FctCat (Δ^op) SetCat@{u p _ _ _ _ _}) 9
    c X _ fin_first last (ordinal_from_first last) a).
  exact triangle_horn_edge_extensions.
Defined.

(** First prove recovery for an abstract final-stage map, so using the
    law later does not expand the entire computed iteration. *)

(** 先对抽象最终阶段映射证明恢复，使后续使用定律时不展开整个计算迭代。 *)

Definition triangle_horn_product_recovery
    (b : TriangleHornStage r 9 ⇒ X)
    (a : TriangleHornStage r 0 ⇒ X)
    (E : (b ∘Nv total_segment) ≈N a)
  : ((b ∘Nv TriangleHornFinalN r) ∘Nv
      RegionInclusionN (TriangleHornRegion r 0)) ≈N a.
Proof.
  intros n x.
  transitivity (b n (total_segment n x)).
  - exact (@func_proper _ _ (b n) _ _ (triangle_horn_initial_segment n x)).
  - exact (E n x).
Defined.

(** Extend the actual old-region map to the entire triangle product.
    Its actual map is the retained nine-fold extension followed by the
    same final-stage inverse; no new universal-property proof is used. *)

(** 将实际旧区域映射延拓到整个三角积。实际映射是保留的九重延拓复合于同一
    最终阶段逆，不另证泛性质。 *)

Definition TriangleHornProductExtension (a : TriangleHornStage r 0 ⇒ X)
  : ∃ b : TriangleHornAmbient ⇒ X,
      (b ∘Nv RegionInclusionN (TriangleHornRegion r 0)) ≈N a
  := let e := triangle_horn_chain_extension_target a in
      (e.1 ∘Nv TriangleHornFinalN r;
        triangle_horn_product_recovery e.1 a e.2).

Local Transparent chain_extension_target TriangleHornStepExtension.

End Iteration.
