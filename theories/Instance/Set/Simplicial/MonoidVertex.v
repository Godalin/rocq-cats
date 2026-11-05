From Cats Require Export
  Instance.Set.Simplicial.Monoid
  Instance.Set.Simplicial.Vertex.
From Cats Require Import
  Cat.Diagram.Core
  Instance.Nat.Order
  Instance.Set.Lift
  Instance.Set.Terminal.

Local Open Scope nat_scope.
Local Open Scope monoid_scope.

(** * Single-Object Chains in the Vertex Nerve *)

(** * 顶点 nerve 中的单对象箭头链 *)

(** The singleton object set has identity transport. It identifies vertices
    without identifying distinct elements of the monoid hom-setoid. *)

(** 单元素对象集合的运输为恒等；它识别顶点，但不识别幺半群 Hom 广集中的不同元素。 *)

Definition MonoidObjectsF@{v q +} (M : SetC@{v q})
    `{HM : !Monoid M}
  : Functor (EqGpd UnitS@{Set Set}) B(M)
  := ConstF (EqGpd UnitS@{Set Set}) (C := B(M)) tt.

(** Regard the monoid category as the induced category on its labelled
    singleton object. All arrow data and operations are retained. *)

(** 将幺半群范畴看成带单元素对象标签的诱导范畴；保留全部箭头数据及运算。 *)

Program Definition MonoidVertexF@{v q +} (M : SetC@{v q})
    `{HM : !Monoid M}
  : Functor B(M) (VertexCat (MonoidObjectsF M))
  :=
  {|F0 x := x
  ; F1 x y f := f
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Interpret the tuple nerve in the general vertex nerve. Naturality is
    the already proved segment-subdivision law. *)

(** 将元组 nerve 解释到一般顶点 nerve；自然性就是已有的段积细分定律。 *)

Program Definition MonoidVertexN@{u p v q +} {M : SetC@{v q}}
    `{HM : !Monoid M}
  : (LiftF ∘F Nₘ(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      Nᵥ(MonoidObjectsF M)
  :=
  {|nt n :=
      {|func xs := ⟨MonoidVertexF M ∘F MonoidChainF (lower xs)⟩ᵥ
      |}
  |}.
Next Obligation.
  intros [xs] [ys] [H]. refine {|lower := _
                              |}.
  exists (λ i, tt). intros i j a.
  change (1 ⋅ xs⟦i, j⟧⋅ ≈S ys⟦i, j⟧⋅ ⋅ 1).
  rewrite monoid_unit_l, monoid_unit_r.
  apply monoid_segment_proper; [exact H | reflexivity | reflexivity].
Defined.
Next Obligation.
  intros [xs]. refine {|lower := _
                      |}.
  exists (λ i, tt). intros i j a.
  change (1 ⋅ xs[f]M⟦i, j⟧⋅ ≈S xs⟦f i, f j⟧⋅ ⋅ 1).
  rewrite monoid_unit_l, monoid_unit_r.
  apply monoid_segment_sub.
  - apply ordinal_functor_monotone.
  - exact (nat_le_to_le a).
Defined.

(** The general vertex nerve reflects the original tuple equality. Thus
    its comparison does not collapse distinct monoid loops or chains. *)

(** 一般顶点 nerve 反映原来的元组相等，因此此比较不压缩不同的幺半群环路或箭头链。 *)

Lemma monoid_vertex_reflects@{u p v q +} {M : SetC@{v q}}
    `{HM : !Monoid M} {n : nat} (xs ys : M ^S n)
  : (MonoidVertexN : (LiftF ∘F Nₘ(M) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ _) n
        {|lower := xs
        |} ≈S MonoidVertexN n {|lower := ys
                              |} → xs ≈S ys.
Proof.
  intros [[e H]] i. specialize (H _ _ (ordinal_step i)).
  change (1 ⋅ xs⟦fin_weaken i, fin_next i⟧⋅ ≈S
    ys⟦fin_weaken i, fin_next i⟧⋅ ⋅ 1) in H.
  rewrite monoid_unit_l, monoid_unit_r, !monoid_segment_step in H.
  exact H.
Defined.

(** Forgetting labels commutes with the earlier chain-to-diagram map. *)

(** 忘却标签与原来的箭头链到图式映射相容。 *)

Lemma monoid_vertex_diagram@{u p v q +} {M : SetC@{v q}}
    `{HM : !Monoid M}
  : (VertexDiagramN (MonoidObjectsF M) ∘Nv MonoidVertexN :
      (LiftF ∘F Nₘ(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ _) ≈N
      MonoidDiagramN.
Proof.
  intros n [xs]. refine {|lower := _
                         |}.
  apply monoid_diagram_iso. intros i j f. reflexivity.
Defined.

(** Extract consecutive arrows from a labelled singleton diagram. *)

(** 从带单元素对象标签的图式提取相邻箭头。 *)

Definition monoid_vertex_chain@{v q +} {M : SetC@{v q}}
    `{HM : !Monoid M} {n : nat}
    (F : Functor [Ord n] (VertexCat (MonoidObjectsF M)))
  : M ^S n
  := λ i, fmap F (ordinal_step i).

(** Reconstructing a diagram from its consecutive arrows gives labelled
    equality. All longer intervals follow from ordinal naturality. *)

(** 从相邻箭头重构图式得到带标签的相等；更长区间全部由序数自然性导出。 *)

Definition monoid_vertex_reconstruct@{v q +} {M : SetC@{v q}}
    `{HM : !Monoid M} {n : nat}
    (F : Functor [Ord n] (VertexCat (MonoidObjectsF M)))
  : VertexDiagramEq (MonoidObjectsF M)
      (MonoidVertexF M ∘F MonoidChainF (monoid_vertex_chain F)) F.
Proof.
  exists (λ i, tt). apply ordinal_naturality_steps. intros i.
  change (1 ⋅ (monoid_vertex_chain F)⟦fin_weaken i, fin_next i⟧⋅ ≈S
    fmap F (ordinal_step i) ⋅ 1).
  rewrite monoid_unit_l, monoid_unit_r, monoid_segment_step. reflexivity.
Defined.

(** Every diagram arrow is the segment product of its adjacent arrows. *)

(** 每条图式箭头均为其相邻箭头的段积。 *)

Lemma monoid_vertex_segment@{v q +} {M : SetC@{v q}}
    `{HM : !Monoid M} {n : nat}
    (F : Functor [Ord n] (VertexCat (MonoidObjectsF M)))
    (i j : Ordinal n) (f : (@Hom [Ord n]) i j)
  : (monoid_vertex_chain F)⟦i, j⟧⋅ ≈S fmap F f.
Proof.
  pose proof ((monoid_vertex_reconstruct F).2 i j f) as H.
  change (1 ⋅ (monoid_vertex_chain F)⟦i, j⟧⋅ ≈S fmap F f ⋅ 1) in H.
  rewrite monoid_unit_l, monoid_unit_r in H. exact H.
Defined.

(** Adjacent-arrow extraction commutes with arbitrary simplex restriction. *)

(** 相邻箭头提取与任意单纯限制交换。 *)

Program Definition VertexMonoidN@{u p v q +} {M : SetC@{v q}}
    `{HM : !Monoid M}
  : (Nᵥ(MonoidObjectsF M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      (LiftF ∘F Nₘ(M))
  :=
  {|nt n :=
      {|func F :=
          {|lower := monoid_vertex_chain (lower F)
          |}
      |}
  |}.
Next Obligation.
  intros [F] [G] [[e H]]. refine {|lower := _
                                |}.
  intros i. specialize (H _ _ (ordinal_step i)).
  change (1 ⋅ fmap F (ordinal_step i) ≈S
    fmap G (ordinal_step i) ⋅ 1) in H.
  rewrite monoid_unit_l, monoid_unit_r in H. exact H.
Defined.
Next Obligation.
  intros [F]. refine {|lower := _
                      |}.
  intros i. symmetry. exact (monoid_vertex_segment F _ _
    (fmap f (ordinal_step i))).
Defined.

(** The singleton specialization recovers exactly the original tuple nerve,
    up to a natural isomorphism at common value sizes. *)

(** 在共同值大小中，单对象特化通过自然同构恰好恢复原来的元组 nerve。 *)

Definition monoid_vertex_iso@{u p v q +} {M : SetC@{v q}}
    `{HM : !Monoid M}
  : (LiftF ∘F Nₘ(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      Nᵥ(MonoidObjectsF M).
Proof.
  exists MonoidVertexN. intros n. exists (VertexMonoidN n). split.
  - intros [xs]. refine {|lower := _
                         |}.
    intros i. apply monoid_segment_step.
  - intros [F]. exact {|lower := monoid_vertex_reconstruct F
                       |}.
Defined.
