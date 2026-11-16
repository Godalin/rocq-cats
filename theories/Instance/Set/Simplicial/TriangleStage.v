From Cats Require Export
  Instance.Set.Simplicial.TriangleHorn
  Instance.Set.PresheafRegionUnion.
From Cats Require Import
  Cat.Core.
From Stdlib Require Import
  Lia.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * The Nine Regions as Actual Presheaves

    [triangle_horn_stage_preimage_iff] supplies the exact horn preimages
    of the coordinate cells. Here those Type-valued regions become actual
    subpresheaves of the triangle product. Equalities compare coordinates,
    retaining all stage, cell and horn witnesses as computational data.

    The next chapter's
    %\coqref{Cats.Instance.Set.Simplicial.TriangleAttachment.triangle horn attachment pushout}
    {%[triangle_horn_attachment_pushout]%}% specializes the union pushout
    to a horn attachment; the region equivalences here do not themselves
    assert that pushout.

    In the diagram, A_s is the old stage, N_s the supplied cell image,
    and d_s is its dimension. Both comparisons preserve the same two
    ambient coordinates; their inverses recover retained factors or
    change membership witnesses, without equating those witnesses. *)

(** * 九个区域的实际预层

    [triangle_horn_stage_preimage_iff] 给出坐标单形的精确 horn 原像。此处将
    这些 Type 值区域实现为三角积的实际子预层。相等比较坐标，同时保留阶段、
    单形和 horn 见证作为计算数据。

    下一章的
    %\coqref{Cats.Instance.Set.Simplicial.TriangleAttachment.triangle horn attachment pushout}
    {%[triangle_horn_attachment_pushout]%}% 将交并推出特化为 horn 附着；本章
    区域之间的等价本身尚未断言该推出。

    图中 A_s 是旧阶段，N_s 是给定单形像，d_s 是其维数。两个比较都保留同一对
    环境坐标；逆映射恢复保留的因子或改变隶属见证，不等同这些见证。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\Delta[d_s] \arrow[r,"\cong"] \arrow[dr,"c_s"']
  & N_s \arrow[d,hook] \\
& \Delta[2]\times\Delta[2]
\end{tikzcd}
\qquad
\begin{tikzcd}[column sep=large]
A_{s+1} \arrow[r,"\cong"] & A_s\cup N_s
\end{tikzcd}
\end{center}%
*)

(** The common ambient presheaf keeps the two value bounds independent. *)

(** 共同环境预层保持两个取值界独立。 *)

Definition TriangleHornAmbient@{u p +}
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialParameterF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2.

(** The raw stage's existing transport and restriction realize its region. *)

(** 原阶段已有的运输与限制给出其实际区域。 *)

Program Definition TriangleHornRegion@{u p +} (r : Ordinal 2) (k : nat)
  : PresheafRegion (TriangleHornAmbient@{u p _ _ _ _ _ _ _})
  :=
  {|region_member n x := is_triangle_horn_stage r k
      (lower (fst x)) (lower (snd x))
  ; region_precomp n m θ x H := triangle_horn_stage_pre r k
      (lower (fst x)) (lower (snd x)) θ H
  |}.
Next Obligation.
  intros [[a] [b]] [[a'] [b']] [[E] [F]]. split.
  - exact (triangle_horn_stage_transport r k a a' b b' E F).
  - exact (triangle_horn_stage_transport r k a' a b' b
      (symmetry E) (symmetry F)).
Defined.

(** Stage membership is retained in the actual carrier. *)

(** 实际载体保留阶段隶属。 *)

Definition TriangleHornStage@{u p +} (r : Ordinal 2) (k : nat)
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := RegionPsh (TriangleHornRegion r k).

(** ** One Supplied Cell

    Fix a missing parameter face and one of the nine steps. A cell image
    retains its actual factor operator and both coordinate equations.
    Joint coordinate injectivity will recover that factor respectfully. *)

(** ** 一个给定单形

    固定参数缺面及九步之一。单形像保留实际因子算子与两坐标方程；双坐标联合
    单射性将保相等地恢复该因子。 *)

Section StageCell.
Universes u p.
Context (r : Ordinal 2) (s : Ordinal 8).

(** A point in the image supplies a factor, rather than mere existence. *)

(** 像中的点给出一个实际因子，而非仅有存在性。 *)

Program Definition TriangleHornCellRegion
  : PresheafRegion (TriangleHornAmbient@{u p _ _ _ _ _ _ _})
  :=
  {|region_member n x :=
      ∃ h : (@Hom Δ) n (S (simplex_triangle_horn_face_dim s)),
        (lower (fst x) ≈ SimplexTriangleHornSpaceF r s ∘ h) ∧
        (lower (snd x) ≈ SimplexTriangleHornTimeF r s ∘ h)
  ; region_precomp n m θ x H :=
      (H.1 ∘ θ; (ltac:(rewrite <- comp_assoc; apply comp_r; exact (fst H.2)),
                   ltac:(rewrite <- comp_assoc; apply comp_r; exact (snd H.2))))
  |}.
Next Obligation.
  intros [[a] [b]] [[a'] [b']] [[E] [F]]. split; intros [h [A B]]; exists h;
    split.
  - transitivity a; [symmetry; exact E | exact A].
  - transitivity b; [symmetry; exact F | exact B].
  - transitivity a'; [exact E | exact A].
  - transitivity b'; [exact F | exact B].
Defined.

(** Yoneda reads both actual coordinates of the cell. *)

(** Yoneda 读取单形的两个实际坐标。 *)

Definition TriangleHornCellN
  : (Δ[S (simplex_triangle_horn_face_dim s)] :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ TriangleHornAmbient
  := ⟦({|lower := SimplexTriangleHornSpaceF r s|},
        {|lower := SimplexTriangleHornTimeF r s|})⟧Δ[TriangleHornAmbient;
      S (simplex_triangle_horn_face_dim s)].

(** The actual map lands in the supplied image region. *)

(** 实际映射落在给定像区域内。 *)

Definition TriangleHornCellImageN
  : (Δ[S (simplex_triangle_horn_face_dim s)] :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ RegionPsh TriangleHornCellRegion
  := RegionFactorN TriangleHornCellRegion TriangleHornCellN
      (λ n h, (lower h; (reflexivity _, reflexivity _))).

(** Recover the retained factor. Different witnesses give specified-equal
    operators by the integrated joint-coordinate injectivity theorem. *)

(** 恢复保留的因子。不同见证由已有双坐标联合单射定理给出指定相等的算子。 *)

Program Definition TriangleHornCellInverseN
  : RegionPsh TriangleHornCellRegion ⇒
      (Δ[S (simplex_triangle_horn_face_dim s)] :
        Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  :=
  {|nt n := {|func x := {|lower := x.2.1|}|}
  |}.
Next Obligation.
  intros [[[a] [b]] [h [A B]]] [[[a'] [b']] [h' [A' B']]] [[E] [F]].
  refine {|lower := _|}. apply (triangle_horn_cell_factors_eq r s).
  - transitivity a; [symmetry; exact A |].
    transitivity a'; [exact E | exact A'].
  - transitivity b; [symmetry; exact B |].
    transitivity b'; [exact F | exact B'].
Defined.
Next Obligation. intros x. reflexivity. Defined.

(** The two maps retain the original standard simplex, up to natural iso. *)

(** 两映射按自然同构保留原标准单形。 *)

Definition triangle_horn_cell_image_iso
  : TriangleHornCellImageN ⦂
      Δ[S (simplex_triangle_horn_face_dim s)] ≅N RegionPsh TriangleHornCellRegion.
Proof.
  apply is_iso_nat_iso. exists TriangleHornCellInverseN. split.
  - intros n [h]. reflexivity.
  - intros n [[[a] [b]] [h [A B]]].
    split; refine {|lower := _|}; symmetry; assumption.
Defined.

(** The old stage and this cell image have an actual union. *)

(** 旧阶段与本单形像有实际的并。 *)

Definition TriangleHornStepUnion
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := RegionPsh (RegionUnion (TriangleHornRegion r (fin_rank s))
      TriangleHornCellRegion).

(** Split the next-stage witness into an old point or the current cell.
    Finite-position equality is decided transparently; rank injectivity
    is used only in the old-stage bound, never to transport cell data. *)

(** 将下一阶段见证拆成旧点或当前单形；有限位置相等透明地判定。编号单射只用于
    旧阶段的界，不用于运输单形数据。 *)

Definition triangle_horn_next_union n
    (x : TriangleHornAmbient@{u p _ _ _ _ _ _ _} n)
    (H : region_member (TriangleHornRegion r (S (fin_rank s))) x)
  : region_member (RegionUnion (TriangleHornRegion r (fin_rank s))
      TriangleHornCellRegion) x.
Proof.
  destruct H as [B | [t [K [h E]]]].
  - left. left. exact B.
  - destruct (ltac:(repeat decide equality) : {t = s} + {t <> s}) as [J | J].
    + subst t. right. exact (h; E).
    + left. right. exists t. split; [| exact (h; E)].
      assert (L : fin_rank t <> fin_rank s).
      { intros L. apply J. exact (fin_rank_injective t s L). }
      lia.
Defined.

(** Conversely both union alternatives belong to the next stage. *)

(** 反之，并的两个分支都属于下一阶段。 *)

Definition triangle_horn_union_next n
    (x : TriangleHornAmbient@{u p _ _ _ _ _ _ _} n)
    (H : region_member (RegionUnion (TriangleHornRegion r (fin_rank s))
      TriangleHornCellRegion) x)
  : region_member (TriangleHornRegion r (S (fin_rank s))) x.
Proof.
  destruct H as [H | H].
  - exact (triangle_horn_stage_mono r (fin_rank s) (S (fin_rank s))
      (ltac:(lia)) _ _ H).
  - right. exists s. split; [lia | exact H].
Defined.

(** Both comparison maps preserve the same coordinates. *)

(** 两个比较映射保留同一坐标。 *)

Definition TriangleHornNextUnionN
  : TriangleHornStage r (S (fin_rank s)) ⇒ TriangleHornStepUnion
  := RegionMapN (R := TriangleHornRegion r (S (fin_rank s)))
      (S := RegionUnion (TriangleHornRegion r (fin_rank s)) TriangleHornCellRegion)
      triangle_horn_next_union.

(** The inverse only changes the retained membership data. *)

(** 逆映射只改变保留的隶属数据。 *)

Definition TriangleHornUnionNextN
  : TriangleHornStepUnion ⇒ TriangleHornStage r (S (fin_rank s))
  := RegionMapN
      (R := RegionUnion (TriangleHornRegion r (fin_rank s)) TriangleHornCellRegion)
      (S := TriangleHornRegion r (S (fin_rank s))) triangle_horn_union_next.

(** The new stage is naturally isomorphic to the union, without witness
    equality or any selected Kan fillers. *)

(** 新阶段与该并自然同构，无需见证相等或任何选定 Kan 填充。 *)

Definition triangle_horn_next_union_iso
  : TriangleHornNextUnionN ⦂ TriangleHornStage r (S (fin_rank s)) ≅N
      TriangleHornStepUnion.
Proof.
  apply is_iso_nat_iso. exists TriangleHornUnionNextN.
  split; intros n [x H]; change (x ≈S x); reflexivity.
Defined.

(** The actual old-stage inclusion is a coordinate-preserving region map. *)

(** 实际旧阶段包含是保留坐标的区域映射。 *)

Definition TriangleHornStageInclusionN
  : TriangleHornStage r (fin_rank s) ⇒ TriangleHornStage r (S (fin_rank s))
  := RegionMapN (R := TriangleHornRegion r (fin_rank s))
      (S := TriangleHornRegion r (S (fin_rank s)))
      (λ n x H, triangle_horn_stage_mono r (fin_rank s) (S (fin_rank s))
        (ltac:(lia)) _ _ H).

(** The attached standard simplex has its actual next-stage coordinate map. *)

(** 附着的标准单形具有进入下一阶段的实际坐标映射。 *)

Definition TriangleHornStageCellN
  : (Δ[S (simplex_triangle_horn_face_dim s)] :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ TriangleHornStage r (S (fin_rank s)).
Proof.
  refine (RegionFactorN (TriangleHornRegion r (S (fin_rank s)))
    TriangleHornCellN _).
  intros n [h]. right. exists s. split; [lia |].
  exists h. split; reflexivity.
Defined.

(** The exact raw preimage constructs the actual attaching map on the horn. *)

(** 精确原像构造 horn 上的实际附着映射。 *)

Definition TriangleHornAttachingN
  : (Λ[S (simplex_triangle_horn_face_dim s); simplex_triangle_horn_missing r s] :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ TriangleHornStage r (fin_rank s)
  := RegionFactorN (TriangleHornRegion r (fin_rank s))
      (TriangleHornCellN ∘Nv ιΛ[S (simplex_triangle_horn_face_dim s);
        simplex_triangle_horn_missing r s])
      (λ n h, triangle_horn_stage_from_horn r s (lower h).1 (lower h).2).

(** The square commutes by coordinates, before any target or Kan choice. *)

(** 方形按坐标交换，在此之前无需任何目标或 Kan 选择。 *)

Definition triangle_horn_attachment_comm
  : (TriangleHornStageInclusionN ∘Nv TriangleHornAttachingN) ≈N
      (TriangleHornStageCellN ∘Nv ιΛ[S (simplex_triangle_horn_face_dim s);
        simplex_triangle_horn_missing r s]).
Proof. intros n h. split; reflexivity. Defined.

End StageCell.

(** Every actual product simplex belongs to stage nine by the existing
    cover. Its inverse to inclusion keeps both coordinates unchanged. *)

(** 已有覆盖使每个实际积单形属于第九阶段；包含的逆保留两个坐标。 *)

Definition TriangleHornFinalN@{u p +} (r : Ordinal 2)
  : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      TriangleHornStage r 9
  := RegionFactorN (TriangleHornRegion r 9) IdN
      (λ n x, triangle_horn_stage_complete r (lower (fst x)) (lower (snd x))).

(** Thus the final stage recovers the full actual product naturally,
    without identifying any law or membership fields. *)

(** 因此最终阶段自然地恢复完整实际积，无需等同任何定律或隶属字段。 *)

Definition triangle_horn_final_iso@{u p +} (r : Ordinal 2)
  : RegionInclusionN (TriangleHornRegion r 9) ⦂
      (TriangleHornStage r 9 : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      TriangleHornAmbient.
Proof.
  apply is_iso_nat_iso. exists (TriangleHornFinalN r). split.
  - intros n [x H]. change (x ≈S x). reflexivity.
  - intros n x. change (x ≈S x). reflexivity.
Defined.
