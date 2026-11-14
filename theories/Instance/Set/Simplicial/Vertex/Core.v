From Cats Require Export
  Instance.Set.Vertex.Core
  Instance.Set.Simplicial.Operators.
From Cats Require Import
  Instance.Set.Lift
  Instance.Set.Simplicial.Nerve.

Local Open Scope nat_scope.

(** * The Nerve with Specified Vertex Equality

    The input object action supplies the equality and coherent transport
    missing from a bare category. Simplices retain their vertex labels and
    compare arrow data only using these prescribed transports. No change
    is made to the natural-isomorphism equality of general functors. *)

(** * 具有指定顶点相等的 nerve

    输入的对象作用提供单独一个范畴所缺少的对象相等与相干运输。单形保留顶点
    标签，并且只通过这些指定运输比较箭头数据；一般函子的自然同构相等保持不变。 *)

(** ** From the Chain Picture to Specified Labels

    Recall %\coqref{Cats.Instance.Set.Simplicial.Nerve.DiagramNerve}
    {%[DiagramNerve]%}%: its simplices are ordinal diagrams, compared by
    natural isomorphism. Here each vertex instead carries a label in a
    setoid X. The input [T : Fct (EqGpd X) C] tells us both what object
    a label denotes and how a specified equality of labels transports
    arrows. This is why the construction takes T, rather than only C.

    For example, an edge has a source label, a target label and an arrow
    between their interpreted objects. Comparing two such edges first
    compares their labels, then compares their arrows after the prescribed
    transport. An unrelated isomorphism in C cannot substitute for that
    label equality.

    After %\coqref{Cats.Instance.Set.Simplicial.Vertex.Core.VertexNerve}
    {%[VertexNerve]%}%, read %\coqref{Cats.Instance.Set.Simplicial.Vertex.Point.point simplex resp}
    {%[point_simplex_resp]%}% and %\coqref{Cats.Instance.Set.Simplicial.Vertex.Edge.edge simplex resp}
    {%[edge_simplex_resp]%}%
    in the next chapters for the zero- and one-dimensional descriptions.
    Then %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.vertex spine iso}
    {%[vertex_spine_iso]%}% makes the chain picture precise in every degree.
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Reconstruction.vertex nerve hom iso}
    {%[vertex_nerve_hom_iso]%}% is a later reconstruction result; it is not needed
    to understand what an individual nerve simplex is. *)

(** ** 从箭头链图像到指定标签

    回顾 %\coqref{Cats.Instance.Set.Simplicial.Nerve.DiagramNerve}
    {%[DiagramNerve]%}%：其单形是序数图式，按自然同构比较。这里则让每个
    顶点带有广集 X 中的标签。输入 [T : Fct (EqGpd X) C] 同时说明标签
    表示哪个对象，以及指定的标签相等如何运输箭头。因此，构造的输入是 T，
    而不只是 C。

    例如，一条边包含源标签、目标标签，以及对应对象之间的箭头。比较两条边时，
    先比较标签，再沿指定运输比较箭头。C 中无关的对象同构不能替代标签相等。

    读过 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Core.VertexNerve}
    {%[VertexNerve]%}% 后，可先看后续章节的 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Point.point simplex resp}
    {%[point_simplex_resp]%}% 与
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Edge.edge simplex resp}
    {%[edge_simplex_resp]%}%，理解零、一维数据，再用 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.vertex spine iso}
    {%[vertex_spine_iso]%}% 把箭头链
    图像推广到各维。%\coqref{Cats.Instance.Set.Simplicial.Vertex.Reconstruction.vertex nerve hom iso}
    {%[vertex_nerve_hom_iso]%}% 是稍后的重构结果；理解单个 nerve
    单形时还不需要它。 *)

(** Pointwise equal ordinal positions induce labelled equality after
    restriction. Native equality is used only for concrete finite positions. *)

(** 逐点相等的序数位置在限制后诱导带标签的相等；原生相等只用于具体有限位置。 *)

Definition vertex_ordinal_precomp_eq {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C) {m n : nat}
    (θ φ : Fct [Ord m] [Ord n]) (H : ∀ i, θ i = φ i)
    (F : Fct [Ord n] (VertexCat T))
  : VertexDiagramEq T (F ∘F θ) (F ∘F φ).
Proof.
  assert (e : ∀ i, (F (θ i) : X) ≈S F (φ i)).
  { intros i. rewrite (H i). reflexivity. }
  pose (α := OrdinalCompareN θ φ (λ i, f_equal fin_rank (H i))).
  refine (vertex_diagram_comparison T
    (F := F ∘F θ) (G := F ∘F φ) e (F ∘Nl α) _).
  intros i. change (fmap F (α i) ≈ T⟦e i⟧Ob).
  generalize (e i), (α i). rewrite <- (H i). intros p a.
  rewrite vertex_transport_id.
  transitivity (fmap F (@Cats.Cat.Core.id [Ord n] (θ i))).
  - apply functor_fmap_proper. exact tt.
  - apply functor_id.
Defined.

(** Constant restrictions compare by their single vertex. Their arrows
    become identities even when the order witnesses are different. *)

(** 常值限制按唯一顶点比较；即使顺序见证不同，其箭头也都成为恒等。 *)

Definition vertex_constant_precomp_eq {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C) {m n k : nat}
    (F : Fct [Ord n] (VertexCat T))
    (G : Fct [Ord k] (VertexCat T))
    (u : Fct [Ord m] [Ord n]) (v : Fct [Ord m] [Ord k])
    (a : Ordinal n) (b : Ordinal k)
    (Hu : ∀ i, u i = a) (Hv : ∀ i, v i = b)
    (e : (F a : X) ≈S G b)
  : VertexDiagramEq T (F ∘F u) (G ∘F v).
Proof.
  assert (d : ∀ i, (F (u i) : X) ≈S G (v i)).
  { intros i. rewrite (Hu i), (Hv i). exact e. }
  exists d. intros i j f.
  change (T⟦d j⟧Ob ∘ fmap F (fmap u f) ≈
    fmap G (fmap v f) ∘ T⟦d i⟧Ob).
  generalize (d i), (d j), (fmap u f), (fmap v f).
  rewrite (Hu i), (Hu j), (Hv i), (Hv j).
  intros p q g h.
  rewrite (@functor_fmap_proper _ _ F a a g id tt),
    (@functor_fmap_proper _ _ G b b h id tt),
    !functor_id, comp_id_l, comp_id_r.
  apply vertex_transport_witness_independent.
Defined.

(** Restriction of labelled ordinal diagrams is a simplicial setoid.
    Native diagram and equality sizes are raised separately to the chosen
    value sizes; this is an ordinary size inclusion, not resizing. *)

(** 带标签的序数图式及其限制构成单纯广集；原生图式及相等分别提升至所选值大小，
    这是通常的大小嵌入，不是大小重设。 *)

Program Definition VertexNerve@{u p +} {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  :=
  {|F0 n := LiftS (VertexDiagramS T [Ord n])
  ; F1 n m θ := (vertex_diagram_precomp_resp T θ)^↑S
  |}.
Next Obligation.
  intros θ φ H [F]. refine {|lower := _
                           |}.
  apply vertex_ordinal_precomp_eq. exact (fst (simplex_eq_iff θ φ) H).
Defined.
Next Obligation.
  intros [F]. refine {|lower := _
                     |}.
  exists (λ i, reflexivity (F i : X)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.
Next Obligation.
  intros [F]. refine {|lower := _
                     |}.
  exists (λ i, reflexivity (F (g (f i)) : X)). intros i j a.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

Notation "'Nᵥ(' T ')'" := (VertexNerve T) : ob_scope.

(** Include a labelled ordinal diagram as a simplex. *)

(** 将带标签的序数图式作为单形。 *)

Definition VertexSimplex@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C} {n : nat}
    (F : Fct [Ord n] (VertexCat T))
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n
  :=
  {|lower := F
  |}.

Notation "'⟨' F '⟩ᵥ'" := (VertexSimplex F) : hom_scope.

(** Including a diagram preserves its specified vertex equality. *)

(** 将图式作为单形保持其指定的顶点相等。 *)

Global Instance vertex_simplex_proper@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C} {n : nat}
  : Proper (VertexDiagramEq T ==>
      carrier_equiv ((Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n))
      (@VertexSimplex X C T n).
Proof.
  intros F G e. exact {|lower := e
                      |}.
Defined.

(** A simplex comparison is determined by its vertex equalities and the
    squares on consecutive arrows. All longer intervals follow from the
    general generating-arrow theorem, not from extra simplex fields. *)

(** 单形比较由顶点相等与相邻箭头上的交换方块确定；所有更长区间由一般生成箭头
    定理导出，不需要额外的单形字段。 *)

Lemma vertex_simplex_eq_steps@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C} {n : nat}
    (x y : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : x ≈S y ↔
      ∃ e : ∀ i, (lower x i : X) ≈S lower y i,
        ∀ i : Fin@{Set} n,
          T⟦e (fin_next i)⟧Ob ∘ fmap (lower x) (ordinal_step i) ≈
            fmap (lower y) (ordinal_step i) ∘ T⟦e (fin_weaken i)⟧Ob.
Proof.
  split.
  - intros [[e H]]. exists e. intros i. apply H.
  - intros [e H]. refine {|lower := (e; _)
                         |}.
    exact (ordinal_naturality_steps (lower x) (lower y)
      (λ i, T⟦e i⟧Ob) H).
Defined.

(** Zero-simplices compare exactly by the equality of their sole vertices. *)

(** 零维单形恰按唯一顶点的指定相等比较。 *)

Lemma vertex_nerve_zero_eq_iff@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C}
    (x y : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 0)
  : x ≈S y ↔ (lower x fin_first : X) ≈S lower y fin_first.
Proof.
  split.
  - intros [[e H]]. exact (e fin_first).
  - intros H. apply (snd (vertex_simplex_eq_steps x y)).
    assert (e : ∀ i, (lower x i : X) ≈S lower y i).
    { intros [[] | []]. exact H. }
    exists e. intros i. destruct i.
Defined.

(** Restriction is precomposition, with the same vertex labels. *)

(** 限制就是保留顶点标签的预复合。 *)

Lemma vertex_nerve_restrict@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C} {m n : nat} (θ : (@Hom Δ) m n)
    (x : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : Nᵥ(T)[θ]Δ x ≈S ⟨lower x ∘F θ⟩ᵥ.
Proof. reflexivity. Defined.

(** Face maps omit a vertex and use the diagram's composite arrow. *)

(** 面映射省略一个顶点，并使用图式中的复合箭头。 *)

Lemma vertex_nerve_face@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C} {n : nat} (i : Ordinal (S n))
    (x : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S n))
  : d[Nᵥ(T); n; i] x ≈S ⟨lower x ∘F δ[n; i]⟩ᵥ.
Proof. apply vertex_nerve_restrict. Defined.

(** Degeneracy maps repeat a vertex and insert its identity arrow. *)

(** 退化映射重复顶点，并插入其恒等箭头。 *)

Lemma vertex_nerve_degeneracy@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C} {n : nat} (i : Ordinal n)
    (x : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : s[Nᵥ(T); n; i] x ≈S ⟨lower x ∘F σ[n; i]⟩ᵥ.
Proof. apply vertex_nerve_restrict. Defined.

(** Forgetting the prescribed vertex comparisons gives the diagram nerve
    of C. The two nerves use a common pair of value universes. *)

(** 忘却指定顶点比较得到 C 的图式 nerve；两种 nerve 使用共同的一对值宇宙。 *)

Program Definition VertexDiagramN@{u p +} {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ N≅(C)
  :=
  {|nt n := (vertex_diagram_forget_resp T)^↑S
  |}.
Next Obligation.
  intros [F]. refine {|lower := _
                      |}.
  symmetry. apply CompF_assoc.
Defined.
