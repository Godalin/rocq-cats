From Cats Require Export
  Cat.Extension.Core
  Instance.Set.Simplicial.Horn.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.

(** * Extending an Actual Map Across One Horn Attachment

    A horn attachment is specified by a pushout square with one leg the
    actual horn inclusion. Fill the restricted old map once, then reuse
    %\coqref{Cats.Cat.Extension.Core.PushoutMapExtension}
    {%[PushoutMapExtension]%}%. The new map is constructed here;
    only the attachment geometry, not a target extension, is input.

    Only the selected filler at this dimension and missing face is used.
    It need not be unique or respectful. The old-region and chosen-cell
    equations are both retained. The next geometric task is to exhibit
    the required finite attachment squares for a parameter triangle
    product; that decomposition and unconditional cylinder reversal or
    composition are not claimed here. *)

(** * 跨一次 horn 附着延拓实际映射

    horn 附着由一个推出方形给定，其中一条腿为实际 horn 包含。将旧映射限制
    到 horn，填充一次，再复用
    %\coqref{Cats.Cat.Extension.Core.PushoutMapExtension}
    {%[PushoutMapExtension]%}%。此处构造新映射；输入只有附着几何，
    不预设目标延拓。

    只使用这个维度、这个缺面的指定填充，不要求其唯一或保持相等。同时保留
    旧区域和选定单形方程。下一几何任务是给出参数三角积所需的有限附着方形；
    此处不声称已经完成该分解或无条件柱反转／复合。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\Lambda[n;r] \arrow[r,"h"] \arrow[d,"\iota_\Lambda"']
  & A \arrow[d,"i"] \arrow[ddr,bend left=25,"a"] & \\
\Delta[n] \arrow[r,"j"'] \arrow[drr,bend right=20,"{\langle w\rangle}"']
  & P \arrow[dr,dashed,"k"] & \\
&& X
\end{tikzcd}
\end{center}%
*)

(** ** Horn Fillers as Extension Targets

    Fix independent carrier/equality sizes and a target simplicial setoid.
    A single supplied horn-filling operation produces extensions of all
    maps from that horn, without choosing other fillers or model structures. *)

(** ** 将 horn 填充作为延拓目标

    固定独立载体／相等大小及目标单纯广集。一份给定的 horn 填充操作延拓该
    horn 的全部映射，不选择其他填充或模型结构。 *)

Section HornExtensionTargets.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (n : nat) (r : Ordinal n).

(** Yoneda exposes the selected filler as an actual extension map. *)

(** Yoneda 将选定填充暴露为实际延拓映射。 *)

Definition horn_extension_target (K : HasHornFillers X n r)
  : is_extension_target (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
      ιΛ[n; r] X.
Proof.
  intros h. exists ⟦(@horn_fill X n r K h).1⟧Δ[X; n].
  exact (@horn_fill X n r K h).2.
Defined.

End HornExtensionTargets.

(** ** A Supplied Attachment Square

    Fix a pushout with an old region A and a newly attached n-simplex.
    No chosen pushouts or injectivity assumptions on the attaching map h
    are required. The target's one horn choice is supplied per extension. *)

(** ** 一个给定附着方形

    固定由旧区域 A 与新附着 n-单形组成的推出。不要求选定推出，也不要求
    附着映射 h 单射；每次延拓显式给定目标的一份 horn 选择。 *)

Section HornAttachments.
Universes u p.
Context {A P X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context {n : nat} {r : Ordinal n}.
Context (h : Λ[n; r] ⇒ A) (i : A ⇒ P) (j : Δ[n] ⇒ P).
Context (HP : is_pushout (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
    h ιΛ[n; r] P i j).

(** Construct the total map from the selected actual horn filler,
    retaining both old-region and selected-simplex restriction equations. *)

(** 从选定实际 horn 填充构造总映射，保留旧区域及选定单形的两个限制方程。 *)

Definition HornAttachmentExtension (K : HasHornFillers X n r) (a : A ⇒ X)
  : ∃ k : P ⇒ X, ((k ∘Nv i) ≈N a) ∧
      ((k ∘Nv j) ≈N (horn_extension_target X n r K (a ∘Nv h)).1)
  := PushoutMapExtension HP a (horn_extension_target X n r K (a ∘Nv h)).

(** Any coherent prescription on a further old subdomain is preserved
    by the constructed map, not merely on its vertices. *)

(** 构造映射保持进一步旧子域上的任意相干给定值，不只是保持其顶点。 *)

Lemma horn_attachment_extension_relative (K : HasHornFillers X n r)
    (a : A ⇒ X) {B : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (s : B ⇒ A) (c : B ⇒ X) (R : (a ∘Nv s) ≈N c)
  : ((HornAttachmentExtension K a).1 ∘Nv (i ∘Nv s)) ≈N c.
Proof.
  exact (map_extension_preserves
    (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
    (fst (HornAttachmentExtension K a).2) s c R).
Defined.

(** Fixing both the old map and the chosen cell value determines the
    total map. This is pushout mediator uniqueness, not filler uniqueness. *)

(** 固定旧映射与选定单形值确定总映射；这是推出中介唯一性，不是填充唯一性。 *)

Lemma horn_attachment_extension_unique (K : HasHornFillers X n r)
    (a : A ⇒ X) (k : P ⇒ X) (E : (k ∘Nv i) ≈N a)
    (F : (k ∘Nv j) ≈N (horn_extension_target X n r K (a ∘Nv h)).1)
  : k ≈N (HornAttachmentExtension K a).1.
Proof.
  apply (pushout_hom_ext HP).
  - transitivity a; [exact E |].
    symmetry. exact (fst (HornAttachmentExtension K a).2).
  - transitivity (horn_extension_target X n r K (a ∘Nv h)).1;
      [exact F | symmetry; exact (snd (HornAttachmentExtension K a).2)].
Defined.

(** Comparing independently selected constructions requires an explicit
    equality of their chosen simplex maps. Choices need not be Proper. *)

(** 比较独立选择的构造时，显式要求选定单形映射相等；选择本身不必为 Proper。 *)

Lemma horn_attachment_extension_proper (K K' : HasHornFillers X n r)
    (a a' : A ⇒ X) (E : a ≈N a')
    (F : (horn_extension_target X n r K (a ∘Nv h)).1 ≈N
      (horn_extension_target X n r K' (a' ∘Nv h)).1)
  : (HornAttachmentExtension K a).1 ≈N (HornAttachmentExtension K' a').1.
Proof. exact (pushout_map_extension_proper HP a a' _ _ E F). Defined.

End HornAttachments.
