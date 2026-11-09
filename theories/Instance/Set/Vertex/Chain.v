From Cats Require Export
  Cat.Chain
  Instance.Set.Vertex.Core.

Local Open Scope nat_scope.

(** * Chains with Specified Vertex Equality

    Chain equality compares vertices by their setoid equality and consecutive
    arrows by squares with the prescribed object transports. Its equivalence
    laws are inherited from labelled diagrams through ordinal reconstruction;
    transport coherence is not reproved for chains. *)

(** * 具有指定顶点相等的箭头链

    链相等以广集相等比较顶点，以指定对象运输的方块比较相邻箭头。其等价律通过
    序数重构继承带标签图式的等价律，不为箭头链重新证明运输相干性。 *)

Section VertexChains.
Context {X : SetC} {C : Cat} (T : Functor (EqGpd X) C).

(** Chain comparisons store only vertex witnesses and consecutive squares. *)

(** 链比较只存储顶点见证与相邻方块。 *)

Definition VertexChainEq {n : nat} (c d : Chain (VertexCat T) n)
  : Type
  := ∃ e : ∀ i, (c i : X) ≈S d i,
      ∀ i : Fin@{Set} n,
        T⟦e (fin_next i)⟧Ob ∘ chain_edge c i ≈
          chain_edge d i ∘ T⟦e (fin_weaken i)⟧Ob.

(** Chain equality is exactly labelled equality of the interpreted diagrams.
    Interval squares follow from the ordinal generating-arrow theorem. *)

(** 链相等恰为所解释图式的带标签相等；区间方块由序数生成箭头定理导出。 *)

Lemma vertex_chain_diagram_eq_iff {n : nat}
    (c d : Chain (VertexCat T) n)
  : VertexChainEq c d ↔ VertexDiagramEq T (⟦c⟧Ch) (⟦d⟧Ch).
Proof.
  split.
  - intros [e H]. exists e.
    apply (ordinal_naturality_steps (⟦c⟧Ch) (⟦d⟧Ch) (λ i, T⟦e i⟧Ob)).
    intros i.
    change (T⟦e (fin_next i)⟧Ob ∘ chain_segment c _ _ (ordinal_step i) ≈
      chain_segment d _ _ (ordinal_step i) ∘ T⟦e (fin_weaken i)⟧Ob).
    rewrite !chain_segment_step. exact (H i).
  - intros [e H]. exists e. intros i.
    pose proof (H _ _ (ordinal_step i)) as Hi.
    change (T⟦e (fin_next i)⟧Ob ∘ chain_segment c _ _ (ordinal_step i) ≈
      chain_segment d _ _ (ordinal_step i) ∘ T⟦e (fin_weaken i)⟧Ob) in Hi.
    rewrite !chain_segment_step in Hi. exact Hi.
Defined.

(** Pull back the already proved diagram equivalence along interpretation. *)

(** 沿解释拉回已经证明的图式等价关系。 *)

Global Instance VertexChainEq_Equivalence {n : nat}
  : Equivalence (@VertexChainEq n).
Proof.
  split.
  - intros c. apply (snd (vertex_chain_diagram_eq_iff c c)). reflexivity.
  - intros c d H. apply (snd (vertex_chain_diagram_eq_iff d c)).
    symmetry. exact (fst (vertex_chain_diagram_eq_iff c d) H).
  - intros c d e H K. apply (snd (vertex_chain_diagram_eq_iff c e)).
    transitivity ⟦d⟧Ch.
    + exact (fst (vertex_chain_diagram_eq_iff c d) H).
    + exact (fst (vertex_chain_diagram_eq_iff d e) K).
Defined.

(** The native setoid of finite chains keeps vertices and arrows as data;
    their comparisons remain Type-valued with independent sizes. *)

(** 原生有限箭头链广集以顶点和箭头为数据，比较保留在独立大小的 Type 中。 *)

Program Definition VertexChainS (n : nat)
  : SetC
  :=
  {|carrier := Chain (VertexCat T) n
  ; carrier_equiv := VertexChainEq
  ; carrier_setoid := VertexChainEq_Equivalence
  |}.

(** Consecutive-arrow extraction preserves labelled diagram equality. *)

(** 相邻箭头提取保持带标签图式相等。 *)

Program Definition vertex_chain_resp (n : nat)
  : VertexDiagramS T [Ord n] →r VertexChainS n
  :=
  {|func F := ⌊F⌋Ch
  |}.
Next Obligation.
  intros F G [e H]. exists e. intros i. exact (H _ _ (ordinal_step i)).
Defined.

(** Interval reconstruction is respectful by the generating-arrow criterion. *)

(** 区间重构由生成箭头判据保持相等。 *)

Program Definition vertex_chain_diagram_resp (n : nat)
  : VertexChainS n →r VertexDiagramS T [Ord n]
  :=
  {|func c := ⟦c⟧Ch
  |}.
Next Obligation.
  intros c d H. exact (fst (vertex_chain_diagram_eq_iff c d) H).
Defined.

(** Extracting a reconstruction recovers the original chain. *)

(** 提取重构结果恢复原箭头链。 *)

Lemma vertex_chain_β {n : nat} (c : VertexChainS n)
  : vertex_chain_resp n (vertex_chain_diagram_resp n c) ≈S c.
Proof.
  exists (λ i, reflexivity (c i : X)). intros i.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  exact (chain_diagram_β c i).
Defined.

(** Reconstructing an extraction recovers the original labelled diagram.
    The identity-component comparison comes from the general chain theory. *)

(** 重构提取结果恢复原带标签图式；恒等分量比较来自一般箭头链理论。 *)

Lemma vertex_chain_η {n : nat} (F : VertexDiagramS T [Ord n])
  : vertex_chain_diagram_resp n (vertex_chain_resp n F) ≈S F.
Proof.
  refine (vertex_diagram_comparison T
    (F := ⟦⌊F⌋Ch⟧Ch) (G := F)
    (λ i, reflexivity (F i : X)) (chain_diagram_η F).1 _).
  intros i. symmetry. apply vertex_transport_id.
Defined.

(** The reconstructed diagram is the unique extension of the chain, up to
    specified labelled equality. No extra mediator choice is stored. *)

(** 重构图式是原链在指定带标签相等下的唯一延拓，不额外存储中介选择。 *)

Definition vertex_chain_universal {n : nat} (c : VertexChainS n)
  : is_unique (R := VertexDiagramEq T)
      (λ F, VertexChainEq ⌊F⌋Ch c) (⟦c⟧Ch).
Proof.
  refine {|this := _
          ; that := _
          |}.
  - exact (vertex_chain_β c).
  - intros F H. transitivity ⟦⌊F⌋Ch⟧Ch.
    + symmetry. exact (vertex_chain_η F).
    + exact (@func_proper _ _ (vertex_chain_diagram_resp n) _ _ H).
Defined.

(** Reindex chains by composing image intervals. Respectfulness follows
    by composing the existing interpretation, restriction and extraction. *)

(** 通过复合像区间重索引箭头链；保持相等由已有解释、限制与提取的复合导出。 *)

Definition vertex_chain_reindex_resp {m n : nat}
    (Q : Functor [Ord m] [Ord n])
  : VertexChainS n →r VertexChainS m
  := vertex_chain_resp m ∘r vertex_diagram_precomp_resp T Q ∘r
      vertex_chain_diagram_resp n.

End VertexChains.
