From Cats Require Export
  Instance.Set.Vertex.Functor
  Cat.Shape.Ordinal.
From Cats Require Import
  Cat.Core
  Cat.Diagram.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Functor
  Instance.Set.Vertex.Terminal.

(** * Specified Vertex Presentations of Finite Ordinals

    Finite positions have native equality. The thin ordinal category gives
    coherent transport along that equality without comparing its witnesses.
    All native data here are small; later nerve values may be raised. *)

(** * 有限序数的指定顶点呈现

    有限位置使用原生相等。薄序数范畴沿此相等给出相干运输，而不比较相等见证。
    此处原生数据均为小数据，之后 nerve 的值可提升到更大宇宙。 *)

(** Equal positions act by the unique ordinal endomorphism. Thin hom
    equality makes this action independent of the native equality witness. *)

(** 相等位置通过唯一序数自同态作用；薄 Hom 相等保证作用不依赖原生相等见证。 *)

Program Definition OrdinalObjectsF (n : nat)
  : Functor (EqGpd (FinS@{Set Set Set} (S n))) [Ord n]
  :=
  {|F0 i := i
  ; F1 i j p := _
  |}.
Next Obligation.
  destruct p. exact (@Cats.Cat.Core.id [Ord n] i).
Defined.
Next Obligation. intros p q H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** A chosen ordinal position defines a map from the terminal presentation. *)

(** 选定序数位置定义一个从终呈现出发的映射。 *)

Program Definition OrdinalVertexPointF (n : nat) (i : Ordinal n)
  : VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set} →ᵥ
      OrdinalObjectsF n
  :=
  {|vertex_functor := ConstF
      (VertexCat VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set})
      (C := VertexCat (OrdinalObjectsF n)) i
  |}.
Next Obligation. intros x y p. reflexivity. Defined.
Next Obligation. exact tt. Defined.

(** Forget the redundant induced-category wrapper, retaining positions
    and arrows exactly. No equality of category records is needed. *)

(** 忘却冗余诱导范畴包装，原样保留位置与箭头，无须范畴记录相等。 *)

Program Definition OrdinalVertexF (n : nat)
  : Functor (VertexCat (OrdinalObjectsF n)) [Ord n]
  :=
  {|F0 i := i
  ; F1 i j f := f
  |}.
Next Obligation. intros f g H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** The inverse view retains the same computational data. *)

(** 反向视图保留相同的可计算数据。 *)

Program Definition OrdinalVertexInvF (n : nat)
  : Functor [Ord n] (VertexCat (OrdinalObjectsF n))
  :=
  {|F0 i := i
  ; F1 i j f := f
  |}.
Next Obligation. intros f g H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** Labelled ordinal diagrams compare precisely by their positions;
    the transport squares hold in the thin target hom equality. *)

(** 带标签的序数图式恰按位置比较，运输方块在薄目标 Hom 相等中成立。 *)

Lemma vertex_ordinal_diagram_eq_iff {J : Cat} (n : nat)
    (P Q : Functor J (VertexCat (OrdinalObjectsF n)))
  : VertexDiagramEq (OrdinalObjectsF n) P Q ↔ ∀ i, P i = Q i.
Proof.
  split.
  - intros [e H]. exact e.
  - intros e. exists e. intros i j f. exact tt.
Defined.

(** Ordinary ordinal diagrams forget only the induced-category wrapper.
    Their natural-isomorphism equality already compares positions. *)

(** 通常的序数图式只忘却诱导范畴包装；其自然同构相等已经按位置比较。 *)

Program Definition vertex_ordinal_diagram_resp (m n : nat)
  : VertexDiagramS (OrdinalObjectsF n) [Ord m] →r
      FunctorS [Ord m] [Ord n]
  :=
  {|func P := OrdinalVertexF n ∘F P
  |}.
Next Obligation.
  intros P Q H. apply (snd (ordinal_functor_iso_iff _ _)).
  exact (fst (vertex_ordinal_diagram_eq_iff n P Q) H).
Defined.

(** Reintroduce labels without choosing any new vertex equality. *)

(** 重新加入标签，无须选取任何新的顶点相等。 *)

Program Definition vertex_ordinal_diagram_inv_resp (m n : nat)
  : FunctorS [Ord m] [Ord n] →r
      VertexDiagramS (OrdinalObjectsF n) [Ord m]
  :=
  {|func P := OrdinalVertexInvF n ∘F P
  |}.
Next Obligation.
  intros P Q H. apply (snd (vertex_ordinal_diagram_eq_iff n _ _)).
  exact (fst (ordinal_functor_iso_iff P Q) H).
Defined.

(** Every monotone map preserves the specified ordinal transport. *)

(** 每个保序映射均保持指定序数运输。 *)

Program Definition OrdinalVertexMapF {m n : nat}
    (θ : Functor [Ord m] [Ord n])
  : OrdinalObjectsF m →ᵥ OrdinalObjectsF n
  :=
  {|vertex_functor := OrdinalVertexInvF n ∘F θ ∘F OrdinalVertexF m
  |}.
Next Obligation. exact tt. Defined.

(** Naturally isomorphic ordinal maps give the prescribed vertex
    comparison, since their positions agree pointwise. *)

(** 自然同构的序数映射逐点位置相等，因此给出指定顶点比较。 *)

Global Instance ordinal_vertex_map_proper {m n : nat}
  : Proper (NatIso ==> VertexFunctorEq) (@OrdinalVertexMapF m n).
Proof.
  intros θ φ H.
  apply (snd (vertex_ordinal_diagram_eq_iff n _ _)).
  exact (fst (ordinal_functor_iso_iff θ φ) H).
Defined.

(** Identity ordinal maps induce identity presentation maps. *)

(** 恒等序数映射诱导恒等呈现映射。 *)

Lemma ordinal_vertex_map_id (n : nat)
  : VertexFunctorEq (OrdinalVertexMapF (@IdF [Ord n]))
      (VertexIdF (OrdinalObjectsF n)).
Proof.
  apply (snd (vertex_ordinal_diagram_eq_iff n _ _)).
  intros i. reflexivity.
Defined.

(** Composition of ordinal maps induces composition of presentation maps. *)

(** 序数映射的复合诱导呈现映射的复合。 *)

Lemma ordinal_vertex_map_comp {k m n : nat}
    (φ : Functor [Ord m] [Ord n]) (θ : Functor [Ord k] [Ord m])
  : VertexFunctorEq (OrdinalVertexMapF (φ ∘F θ))
      (OrdinalVertexMapF φ ∘Fᵥ OrdinalVertexMapF θ).
Proof.
  apply (snd (vertex_ordinal_diagram_eq_iff n _ _)).
  intros i. reflexivity.
Defined.
