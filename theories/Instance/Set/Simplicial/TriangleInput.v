From Cats Require Export
  Instance.Set.Simplicial.TriangleStage.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Gluing the Complete Initial Triangle Region

    The nine-step extension starts with an actual map on
    [(∂Δ[2] × Δ[2]) ∪ (Δ[2] × Λ[2; r])]. A boundary map and the
    retained time-edge maps provide this input when they agree on all
    overlaps. We reuse
    %\coqref{Cats.Instance.Set.PresheafDescent.PresheafDescendN}
    {%[PresheafDescendN]%}%, rather than assuming that the required initial
    map has already been constructed. This map supplies the actual input
    of %\coqref{Cats.Instance.Set.Simplicial.TriangleIteration.TriangleHornProductExtension}
    {%[TriangleHornProductExtension]%}%.

    Agreement below is stated on actual common time factors. Reducing
    it to the endpoint equations of relative cylinders is a subsequent
    specialization; this module needs no Kan choices. *)

(** * 粘合完整的三角初始区域

    九步延拓从 [(∂Δ[2] × Δ[2]) ∪ (Δ[2] × Λ[2; r])] 上的实际映射
    开始。空间边界映射与保留时间边映射在全部交叠上一致时给出这一输入。
    此处复用任意预层下降
    %\coqref{Cats.Instance.Set.PresheafDescent.PresheafDescendN}
    {%[PresheafDescendN]%}%，不假定所需初始映射已经构造完成。此映射给出
    %\coqref{Cats.Instance.Set.Simplicial.TriangleIteration.TriangleHornProductExtension}
    {%[TriangleHornProductExtension]%}% 所需的实际输入。

    下方在实际共同时间因子上表述一致性；将其化为相对柱的端点方程是后续
    特化。本模块不需要 Kan 选择。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
{\partial\Delta[2]\times\Delta[2]} \arrow[dr,"B"'] \arrow[r]
  & A_0 \arrow[d,dashed,"\mathrm{descend}"]
  & {\Delta[2]\times\Delta[1]} \arrow[l,"{j\ne r}"']
    \arrow[dl,"H_j"] \\
& X &
\end{tikzcd}
\end{center}%
*)

(** ** Actual Boundary and Time-Face Maps

    Fix independent value carrier/equality bounds and the missing time
    face. Generators retain all boundary, face and source-degree data;
    the inherited equality compares only the two ambient coordinates. *)

(** ** 实际边界与时间面映射

    固定独立取值载体／相等界及时间缺面。生成元保留全部边界、面和来源维数
    数据；继承的相等只比较两个环境坐标。 *)

Section InitialInput.
Universes u p.
Context (r : Ordinal 2).
Let D
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[2].
Let Bdy
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialParameterF (∂Δ[2]) 2.
Let Cyl
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialCylinderF D.
Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := TriangleHornStage r 0.
Let I
  : Type
  := ((∃ n, Bdy n) +
      (∃ j : Ordinal 2, (¬ j = r) * (∃ n, Cyl n)))%type.
Let degree (i : I)
  : nat
  := match i with inl x => x.1 | inr x => (snd x.2).1 end.

(** Boundary points and retained time-face points land in stage zero. *)

(** 边界点及保留时间面上的点落在零阶段。 *)

Definition triangle_input_generator (i : I)
  : Q (degree i).
Proof.
  destruct i as [[n [a t]] | [j [Hj [n [a t]]]]].
  - exact ((ι∂[2] n a, t); inl (inl (lower a).2)).
  - refine ((a, {|lower := δ[1; j] ∘ lower t|}); inl (inr _)).
    exists (j; Hj), (lower t). reflexivity.
Defined.

(** The original zero-stage witness computes a covering generator. *)

(** 原零阶段见证计算一份覆盖生成元。 *)

Definition triangle_input_cover
  : is_presheaf_cover triangle_input_generator.
Proof.
  intros n [[[a] [t]] M].
  destruct (fst (triangle_horn_stage_zero_iff r a t) M) as [A | H].
  - exists (inl (n; ({|lower := (a; A)|}, {|lower := t|}))),
      (id : (@Hom Δ) n n).
    split; refine {|lower := _|}; apply comp_id_r.
  - destruct H as [[j Hj] [h E]].
    exists (inr (j; (Hj, (n; ({|lower := a|}, {|lower := h|}))))),
      (id : (@Hom Δ) n n).
    split; [refine {|lower := _|}; apply comp_id_r |].
    refine {|lower := _|}.
    transitivity (δ[1; j] ∘ h); [apply comp_id_r | symmetry; exact E].
Defined.

Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.

(** Only retained faces must agree with B along the spatial boundary. *)

(** 只有保留面需要沿空间边界与 B 一致。 *)

Definition triangle_input_boundary_agreement
    (B : Bdy ⇒ X) (H : Ordinal 2 → Cyl ⇒ X)
  : Type
  := ∀ j, ¬ j = r → ∀ n (a : (∂Δ[2]) n) (t : (Δ[1]) n),
      B n (a, fmap StandardSimplexF δ[1; j] n t) ≈S
        H j n (ι∂[2] n a, t).

(** Equal time images have equal values, for every spatial simplex.
    The omitted face and its value impose no condition. The optional
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.TimeOverlap.cylinder_time_matching_iff}
    {%[cylinder_time_matching_iff]%}% derives this condition exactly from
    agreement at the shared cylinder endpoints, without Kan choices. *)

(** 对每个空间单形，相等时间像具有相等取值；缺失面及其取值不施加条件。
    可选的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.TimeOverlap.cylinder_time_matching_iff}
    {%[cylinder_time_matching_iff]%}% 将此条件与柱的公共端点一致精确等价，
    不需要 Kan 选择。 *)

Definition triangle_input_face_agreement (H : Ordinal 2 → Cyl ⇒ X)
  : Type
  := ∀ j k, ¬ j = r → ¬ k = r → ∀ n (a : D n)
      (t t' : (Δ[1]) n),
      δ[1; j] ∘ lower t ≈ δ[1; k] ∘ lower t' →
      H j n (a, t) ≈S H k n (a, t').

Let values (B : Bdy ⇒ X) (H : Ordinal 2 → Cyl ⇒ X) (i : I)
  : X (degree i)
  := match i with
     | inl x => B x.1 x.2
     | inr x => H x.1 (snd x.2).1 (snd x.2).2
     end.

(** All common representable factors are compatible. Naturality reduces
    them to the two explicit overlap conditions, without witness equality. *)

(** 全部共同可表因子均相容；自然性将其化为两项显式交叠条件，不使用见证相等。 *)

Definition triangle_input_compatible
    (B : Bdy ⇒ X) (H : Ordinal 2 → Cyl ⇒ X)
    (EB : triangle_input_boundary_agreement B H)
    (EH : triangle_input_face_agreement H)
  : presheaf_values_compatible triangle_input_generator (values B H).
Proof.
  intros n [[m [a t]] | [j [Hj [m [a t]]]]]
    [[l [a' t']] | [k [Hk [l [a' t']]]]] f g E.
  - transitivity (B n (fmap Bdy f (a, t))).
    + symmetry. exact (nt_naturality B f (a, t)).
    + transitivity (B n (fmap Bdy g (a', t'))).
      * apply func_proper. exact E.
      * exact (nt_naturality B g (a', t')).
  - transitivity (B n (fmap Bdy f (a, t))).
    + symmetry. exact (nt_naturality B f (a, t)).
    + transitivity (B n (fst (fmap Bdy f (a, t)),
        fmap StandardSimplexF δ[1; k] n (snd (fmap Cyl g (a', t'))))).
      * apply func_proper. split; [reflexivity |].
        refine {|lower := _|}.
        transitivity ((δ[1; k] ∘ lower t') ∘ g).
        -- exact (lower (snd E)).
        -- apply comp_assoc.
      * transitivity (H k n (ι∂[2] n (fst (fmap Bdy f (a, t))),
          snd (fmap Cyl g (a', t')))).
        -- apply EB. exact Hk.
        -- transitivity (H k n (fmap Cyl g (a', t'))).
           ++ apply func_proper. split; [exact (fst E) | reflexivity].
           ++ exact (nt_naturality (H k) g (a', t')).
  - symmetry.
    transitivity (B n (fmap Bdy g (a', t'))).
    + symmetry. exact (nt_naturality B g (a', t')).
    + transitivity (B n (fst (fmap Bdy g (a', t')),
        fmap StandardSimplexF δ[1; j] n (snd (fmap Cyl f (a, t))))).
      * apply func_proper. split; [reflexivity |].
        refine {|lower := _|}.
        transitivity ((δ[1; j] ∘ lower t) ∘ f).
        -- symmetry. exact (lower (snd E)).
        -- apply comp_assoc.
      * transitivity (H j n (ι∂[2] n (fst (fmap Bdy g (a', t'))),
          snd (fmap Cyl f (a, t)))).
        -- apply EB. exact Hj.
        -- transitivity (H j n (fmap Cyl f (a, t))).
           ++ apply func_proper. split; [symmetry; exact (fst E) | reflexivity].
           ++ exact (nt_naturality (H j) f (a, t)).
  - transitivity (H j n (fmap Cyl f (a, t))).
    + symmetry. exact (nt_naturality (H j) f (a, t)).
    + transitivity (H k n (fst (fmap Cyl f (a, t)),
        snd (fmap Cyl g (a', t')))).
      * apply EH; [exact Hj | exact Hk |].
        transitivity ((δ[1; j] ∘ lower t) ∘ f).
        -- symmetry. apply comp_assoc.
        -- transitivity ((δ[1; k] ∘ lower t') ∘ g).
           ++ exact (lower (snd E)).
           ++ apply comp_assoc.
      * transitivity (H k n (fmap Cyl g (a', t'))).
        -- apply func_proper. split; [exact (fst E) | reflexivity].
        -- exact (nt_naturality (H k) g (a', t')).
Defined.

(** The complete initial map is the existing descended mediator. *)

(** 完整初始映射就是已有下降中介。 *)

Definition TriangleInputN
    (B : Bdy ⇒ X) (H : Ordinal 2 → Cyl ⇒ X)
    (EB : triangle_input_boundary_agreement B H)
    (EH : triangle_input_face_agreement H)
  : Q ⇒ X
  := PresheafDescendN triangle_input_generator triangle_input_cover
      (values B H) (triangle_input_compatible B H EB EH).

(** Recover every spatial-boundary value, at every time simplex. *)

(** 在每个时间单形处恢复全部空间边界取值。 *)

Definition triangle_input_boundary_β
    (B : Bdy ⇒ X) (H : Ordinal 2 → Cyl ⇒ X)
    (EB : triangle_input_boundary_agreement B H)
    (EH : triangle_input_face_agreement H)
    n (a : (∂Δ[2]) n) (t : (Δ[2]) n)
  : TriangleInputN B H EB EH n
      (triangle_input_generator (inl (n; (a, t)))) ≈S B n (a, t).
Proof.
  exact (presheaf_descend_β triangle_input_generator triangle_input_cover
    (values B H) (triangle_input_compatible B H EB EH) (inl (n; (a, t)))).
Defined.

(** Recover every retained edge map, including all its degenerate points. *)

(** 恢复每个保留边映射，包括全部退化点。 *)

Definition triangle_input_face_β
    (B : Bdy ⇒ X) (H : Ordinal 2 → Cyl ⇒ X)
    (EB : triangle_input_boundary_agreement B H)
    (EH : triangle_input_face_agreement H)
    j (Hj : ¬ j = r) n (z : Cyl n)
  : TriangleInputN B H EB EH n
      (triangle_input_generator (inr (j; (Hj, (n; z))))) ≈S H j n z.
Proof.
  exact (presheaf_descend_β triangle_input_generator triangle_input_cover
    (values B H) (triangle_input_compatible B H EB EH) (inr (j; (Hj, (n; z))))).
Defined.

(** Generator recovery determines the whole initial map. This is gluing
    uniqueness, not uniqueness of any later Kan extension. *)

(** 生成元恢复决定整个初始映射；这是粘合唯一性，不是后续 Kan 延拓唯一性。 *)

Definition triangle_input_unique
    (B : Bdy ⇒ X) (H : Ordinal 2 → Cyl ⇒ X)
    (EB : triangle_input_boundary_agreement B H)
    (EH : triangle_input_face_agreement H)
    (a : Q ⇒ X)
    (E : ∀ n z, a n (triangle_input_generator (inl (n; z))) ≈S B n z)
    (F : ∀ j (Hj : ¬ j = r) n z,
      a n (triangle_input_generator (inr (j; (Hj, (n; z))))) ≈S H j n z)
  : a ≈N TriangleInputN B H EB EH.
Proof.
  apply (snd (presheaf_cover_map_eq triangle_input_generator
    triangle_input_cover _ _)).
  intros [[n [a0 t]] | [j [Hj [n z]]]].
  - transitivity (B n (a0, t));
      [apply E | symmetry; apply triangle_input_boundary_β].
  - transitivity (H j n z); [apply F | symmetry; apply triangle_input_face_β].
Defined.

(** Pointwise equal boundary maps and retained edge maps give equal
    initial maps; the two sets of agreement witnesses are independent. *)

(** 逐点相等的边界映射及保留边映射给出相等初始映射，两组相容见证保持独立。 *)

Definition triangle_input_proper
    (B B' : Bdy ⇒ X) (H H' : Ordinal 2 → Cyl ⇒ X)
    (EB : triangle_input_boundary_agreement B H)
    (EH : triangle_input_face_agreement H)
    (EB' : triangle_input_boundary_agreement B' H')
    (EH' : triangle_input_face_agreement H')
    (E : B ≈N B') (F : ∀ j, ¬ j = r → H j ≈N H' j)
  : TriangleInputN B H EB EH ≈N TriangleInputN B' H' EB' EH'.
Proof.
  apply presheaf_descend_proper.
  intros [[n z] | [j [Hj [n z]]]]; [exact (E n z) | exact (F j Hj n z)].
Defined.

End InitialInput.
