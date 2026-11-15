From Cats Require Export
  Instance.Set.Simplicial.TriangleStage
  Instance.Set.Simplicial.HornAttachment.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Horn Attachment Squares for All Nine Steps

    The old-region preimage theorem becomes an actual horn map on the
    intersection, via [triangle_horn_stage_preimage_iff]. The cell image
    and next-stage union comparisons let [region_union_pushout] supply
    the horn mediator. [triangle_horn_attachment_ext] detects its
    uniqueness on the old region and the actual new standard simplex.

    Each selected filler extends an old map across this actual square.
    This chapter constructs one step, uniformly for all nine positions;
    iterating the steps and comparing relative cylinders is later work. *)

(** * 九步的实际 horn 附着方形

    [triangle_horn_stage_preimage_iff] 在交上给出实际 horn 映射。借助单形像与
    下一阶段的并比较，[region_union_pushout] 给出 horn 中介；
    [triangle_horn_attachment_ext] 在旧区域和实际新增标准单形上检测其唯一性。

    每份选定填充沿此实际方形延拓旧映射。本章统一构造九个位置中的单步；
    逐步迭代与相对柱比较留待后续。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\Lambda[d_s;m_{r,s}] \arrow[r,"h_s"]
  \arrow[d,"\iota_\Lambda"'] & A_s \arrow[d,"i_s"] \\
\Delta[d_s] \arrow[r,"j_s"'] & A_{s+1}
\end{tikzcd}
\qquad d_s=1+\dim(s).
\end{center}%
*)

(** ** Actual Overlap Maps

    Fix independent value bounds, one parameter missing face and one
    attachment step. No Kan choices or target maps are used in geometry. *)

(** ** 实际交叠映射

    固定独立取值界、参数缺面与一步附着；几何不使用 Kan 选择或目标映射。 *)

Section Attachment.
Universes u p.
Context (r : Ordinal 2) (s : Ordinal 8).

Let O
  : PresheafRegion (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := TriangleHornRegion r (fin_rank s).
Let N
  : PresheafRegion (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := TriangleHornCellRegion r s.

(** Transport the old membership to the retained cell coordinates before
    applying the exact horn-preimage theorem. *)

(** 先将旧隶属运输到保留的单形坐标，再应用精确 horn 原像定理。 *)

Definition triangle_horn_overlap_member n (x : RegionPsh (RegionIntersection O N) n)
  : (snd x.2).1 ∈Sv HornSieve (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s).
Proof.
  apply (fst (triangle_horn_stage_preimage_iff r s (snd x.2).1)).
  exact (triangle_horn_stage_transport r (fin_rank s) _ _ _ _
    (fst (snd x.2).2) (snd (snd x.2).2) (fst x.2)).
Defined.

(** This map retains an actual horn factor at every source degree. *)

(** 此映射在每个来源维数保留实际 horn 因子。 *)

Program Definition TriangleHornOverlapN
  : RegionPsh (RegionIntersection O N) ⇒
      (Λ[S (simplex_triangle_horn_face_dim s); simplex_triangle_horn_missing r s]
        : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  :=
  {|nt n :=
      {|func x := {|lower := ((snd x.2).1; triangle_horn_overlap_member n x)|}
      |}
  |}.
Next Obligation.
  intros x y E.
  exact (@func_proper _ _ (TriangleHornCellInverseN r s n)
    (RegionInterRightN O N n x) (RegionInterRightN O N n y) E).
Defined.
Next Obligation.
  intros x. exact {|lower := @reflexivity _ (@HomEq Δ Y
    (S (simplex_triangle_horn_face_dim s))) _
    (@comp Δ Y X (S (simplex_triangle_horn_face_dim s)) (snd x.2).1 f)|}.
Defined.

(** The overlap recovers the old-stage point in specified equality. *)

(** 交叠按指定相等恢复旧阶段中的点。 *)

Definition triangle_horn_overlap_left
  : (TriangleHornAttachingN r s ∘Nv TriangleHornOverlapN) ≈N
      RegionInterLeftN O N.
Proof.
  intros n x. exact ((snd (triangle_horn_cell_image_iso r s n).2)
    (RegionInterRightN O N n x)).
Defined.

(** Its underlying standard simplex is the same retained cell factor. *)

(** 其底层标准单形就是同一个保留的单形因子。 *)

Definition triangle_horn_overlap_factor
  : (ιΛ[S (simplex_triangle_horn_face_dim s);
      simplex_triangle_horn_missing r s] ∘Nv TriangleHornOverlapN) ≈N
      (TriangleHornCellInverseN r s ∘Nv RegionInterRightN O N).
Proof.
  intros n x. exact {|lower := @reflexivity _ (@HomEq Δ n
    (S (simplex_triangle_horn_face_dim s))) _ (snd x.2).1|}.
Defined.

(** Restriction to the actual old stage and actual standard cell detects
    equality of maps. The coordinate-preserving next-stage cover detects
    equality before substituting any computed mediator. *)

(** 限制到实际旧阶段和实际标准单形检测映射相等；保留坐标的下一阶段覆盖先用于
    抽象映射，再代入任何计算得到的中介。 *)

Definition triangle_horn_attachment_ext
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (k l : TriangleHornStage r (S (fin_rank s)) ⇒ X)
    (E : (k ∘Nv TriangleHornStageInclusionN r s) ≈N
      (l ∘Nv TriangleHornStageInclusionN r s))
    (F : (k ∘Nv TriangleHornStageCellN r s) ≈N
      (l ∘Nv TriangleHornStageCellN r s))
  : k ≈N l.
Proof.
  intros n [x G].
  destruct (triangle_horn_next_union r s n x G) as [J | [h [A B]]].
  - transitivity (k n (TriangleHornStageInclusionN r s n (x; J))).
    + apply (@func_proper _ _ (k n)).
      exact (@reflexivity (TriangleHornAmbient n)
        (carrier_equiv (TriangleHornAmbient n)) _ x).
    + transitivity (l n (TriangleHornStageInclusionN r s n (x; J))).
      * exact (E n (x; J)).
      * apply (@func_proper _ _ (l n)).
        exact (@reflexivity (TriangleHornAmbient n)
          (carrier_equiv (TriangleHornAmbient n)) _ x).
  - destruct x as [[a0] [b0]].
    transitivity (k n (TriangleHornStageCellN r s n {|lower := h|})).
    + apply (@func_proper _ _ (k n)).
      split; refine {|lower := _|}; assumption.
    + transitivity (l n (TriangleHornStageCellN r s n {|lower := h|})).
      * exact (F n {|lower := h|}).
      * apply (@func_proper _ _ (l n)).
        split; refine {|lower := _|}; symmetry; assumption.
Defined.

(** ** Reusing the Union Mediator

    Give arbitrary target maps from the old stage and the standard cell,
    agreeing on the attaching horn. Their values on the image overlap
    are compatible via the actual horn factor above. *)

(** ** 复用并中介

    给定旧阶段与标准单形到任意目标的映射，并要求在附着 horn 上一致。
    上述实际 horn 因子保证其在单形像交叠上的取值相容。 *)

Local Opaque RegionUnionGluingN PresheafDescendN.

Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (a : TriangleHornStage r (fin_rank s) ⇒ X)
    (b : (Δ[S (simplex_triangle_horn_face_dim s)] :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X).
Context (H : (a ∘Nv TriangleHornAttachingN r s) ≈N
    (b ∘Nv ιΛ[S (simplex_triangle_horn_face_dim s);
      simplex_triangle_horn_missing r s])).

(** The intersection equation follows from the horn equation, not from
    any equality of the independently supplied membership witnesses. *)

(** 交上的方程来自 horn 方程，而非独立给定隶属见证之间的相等。 *)

Definition triangle_horn_union_agreement
  : (a ∘Nv RegionInterLeftN O N) ≈N
      ((b ∘Nv TriangleHornCellInverseN r s) ∘Nv RegionInterRightN O N).
Proof.
  intros n x.
  transitivity (a n (TriangleHornAttachingN r s n (TriangleHornOverlapN n x))).
  - apply (@func_proper _ _ (a n)).
    exact (symmetry (triangle_horn_overlap_left n x)).
  - transitivity (b n (ιΛ[S (simplex_triangle_horn_face_dim s);
      simplex_triangle_horn_missing r s] n (TriangleHornOverlapN n x))).
    + exact (H n (TriangleHornOverlapN n x)).
    + exact (@func_proper _ _ (b n) _ _ (triangle_horn_overlap_factor n x)).
Defined.

(** Keep the original union mediator and both recovery equations together,
    by the existing general pushout map-extension construction. *)

(** 通过已有通用推出映射延拓构造，将原并中介与两条恢复方程保留在一起。 *)

Let TriangleHornUnionExtension
  : ∃ t : RegionPsh (RegionUnion O N) ⇒ X,
      ((t ∘Nv RegionUnionLeftN O N) ≈N a) ∧
      ((t ∘Nv RegionUnionRightN O N) ≈N
        (b ∘Nv TriangleHornCellInverseN r s))
  := PushoutMapExtension (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
      (region_union_pushout O N) a
      (b ∘Nv TriangleHornCellInverseN r s;
        symmetry triangle_horn_union_agreement).

(** The intermediate map is that same retained union mediator. *)

(** 中间映射就是同一份保留的并中介。 *)

Let TriangleHornUnionGluingN
  : RegionPsh (RegionUnion O N) ⇒ X
  := TriangleHornUnionExtension.1.

(** Only the region membership is changed before evaluating that gluing. *)

(** 求此粘合的值前，只改变区域隶属数据。 *)

Definition TriangleHornAttachmentN
  : TriangleHornStage r (S (fin_rank s)) ⇒ X
  := TriangleHornUnionGluingN ∘Nv TriangleHornNextUnionN r s.

(** The old restriction is the existing union recovery equation. *)

(** 旧域限制就是已有并恢复方程。 *)

Definition triangle_horn_attachment_β1
  : (TriangleHornAttachmentN ∘Nv TriangleHornStageInclusionN r s) ≈N a.
Proof.
  intros n x.
  transitivity (TriangleHornUnionGluingN n (RegionUnionLeftN O N n x)).
  - apply (@func_proper _ _ (TriangleHornUnionGluingN n)).
    exact (@reflexivity (TriangleHornAmbient n)
      (carrier_equiv (TriangleHornAmbient n)) _ x.1).
  - exact ((fst TriangleHornUnionExtension.2) n x).
Defined.

(** The new restriction recovers b, since its retained factor is the
    original standard-simplex operator. *)

(** 新域限制恢复 b，因为其保留因子就是原标准单形算子。 *)

Definition triangle_horn_attachment_β2
  : (TriangleHornAttachmentN ∘Nv TriangleHornStageCellN r s) ≈N b.
Proof.
  intros n h.
  transitivity (TriangleHornUnionGluingN n
    (RegionUnionRightN O N n (TriangleHornCellImageN r s n h))).
  - apply (@func_proper _ _ (TriangleHornUnionGluingN n)).
    exact (@reflexivity (TriangleHornAmbient n)
      (carrier_equiv (TriangleHornAmbient n)) _ (TriangleHornCellN r s n h)).
  - transitivity (b n (TriangleHornCellInverseN r s n
      (TriangleHornCellImageN r s n h))).
    + exact ((snd TriangleHornUnionExtension.2) n
        (TriangleHornCellImageN r s n h)).
    + exact (@func_proper _ _ (b n) _ _
        ((fst (triangle_horn_cell_image_iso r s n).2) h)).
Defined.

(** Mediator uniqueness uses [triangle_horn_attachment_ext] and the two
    already proved recovery equations, keeping the computed map abstract. *)

(** 中介唯一性使用 [triangle_horn_attachment_ext] 和两条已证恢复方程，将计算
    得到的映射保持抽象。 *)

Definition triangle_horn_attachment_unique
    (k : TriangleHornStage r (S (fin_rank s)) ⇒ X)
    (E : (k ∘Nv TriangleHornStageInclusionN r s) ≈N a)
    (F : (k ∘Nv TriangleHornStageCellN r s) ≈N b)
  : k ≈N TriangleHornAttachmentN.
Proof.
  apply (triangle_horn_attachment_ext k TriangleHornAttachmentN).
  - transitivity a; [exact E |].
    symmetry. exact triangle_horn_attachment_β1.
  - transitivity b; [exact F |].
    symmetry. exact triangle_horn_attachment_β2.
Defined.

Local Transparent RegionUnionGluingN PresheafDescendN.

End Attachment.

(** The existing categorical pushout predicate now holds for the actual
    old stage, actual horn inclusion and actual new standard simplex. *)

(** 已有范畴推出谓词现对实际旧阶段、实际 horn 包含与实际新增标准单形成立。 *)

Definition triangle_horn_attachment_pushout@{u p +}
    (r : Ordinal 2) (s : Ordinal 8)
  : is_pushout (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
      (TriangleHornAttachingN r s)
      ιΛ[S (simplex_triangle_horn_face_dim s); simplex_triangle_horn_missing r s]
      (TriangleHornStage r (S (fin_rank s)))
      (TriangleHornStageInclusionN r s) (TriangleHornStageCellN r s).
Proof.
  split; [exact (triangle_horn_attachment_comm r s) |].
  intros X a b H. exists (TriangleHornAttachmentN r s a b H).
  refine {|this := (triangle_horn_attachment_β1 r s a b H,
                    triangle_horn_attachment_β2 r s a b H)
          ; that := _
          |}.
  intros k [E F].
  exact (triangle_horn_attachment_unique r s a b H k E F).
Defined.

(** [HornAttachmentExtension] now computes an extension across each concrete
    step, using only that step's horn dimension and missing face. Both
    original recovery equations remain. *)

(** [HornAttachmentExtension] 现在计算每个具体步骤的延拓，只使用该步的 horn 维数
    与缺面，保留原有两条恢复方程。 *)

Definition TriangleHornStepExtension@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (r : Ordinal 2) (s : Ordinal 8)
    (K : HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s))
    (a : TriangleHornStage r (fin_rank s) ⇒ X)
  : ∃ k : TriangleHornStage r (S (fin_rank s)) ⇒ X,
      ((k ∘Nv TriangleHornStageInclusionN r s) ≈N a) ∧
      ((k ∘Nv TriangleHornStageCellN r s) ≈N
        (horn_extension_target X (S (simplex_triangle_horn_face_dim s))
          (simplex_triangle_horn_missing r s) K
          (a ∘Nv TriangleHornAttachingN r s)).1)
  := HornAttachmentExtension (TriangleHornAttachingN r s)
      (TriangleHornStageInclusionN r s) (TriangleHornStageCellN r s)
      (triangle_horn_attachment_pushout r s) K a.
