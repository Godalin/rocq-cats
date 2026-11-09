From Cats Require Export
  Cat.Groupoid.Star
  Instance.Set.Simplicial.Matching
  Instance.Set.Simplicial.Vertex.Edge.
From Cats Require Import
  Cat.Diagram.Core
  Instance.Nat.Order.
From Stdlib Require Import
  Arith.Compare_dec
  Arith.PeanoNat
  Lia.

Local Open Scope nat_scope.

(** * Comparing Stars on Horn Faces

    Every retained face contains the omitted face's opposite vertex.
    Overlaps identify its radial arrows through specified transport. *)

(** * 比较 horn 面上的星形

    每个保留面都含有缺失面的对顶点；交叠通过指定运输等同径向箭头。 *)

Section RadialComparisons.
Universes u p.
Context {X : SetC} {C : Cat} (T : Functor (EqGpd X) C)
    `{HC : !IsGroupoid (VertexCat T)}.

(** A labelled diagram equality compares radial transitions using any
    witnesses of the same specified endpoint equalities. *)

(** 带标签图式相等按任意同端点的指定相等见证比较径向过渡。 *)

Lemma vertex_radial_comparison {n : nat}
    (F G : Functor [Ord n] (VertexCat T)) (H : VertexDiagramEq T F G)
    (i j : Ordinal n) (a : (F i : X) ≈S G i) (b : (F j : X) ≈S G j)
  : T⟦b⟧Ob ∘ ρ[F; i; j] ≈ ρ[G; i; j] ∘ T⟦a⟧Ob.
Proof.
  destruct H as [e E].
  rewrite (vertex_transport_witness_independent T a (e i)),
    (vertex_transport_witness_independent T b (e j)).
  exact (ordinal_radial_natural (vertex_diagram_iso T (e; E)).1 i j).
Defined.

(** A common star equals an ordinal diagram once its legs commute with
    that diagram's radial transitions and specified vertex transports. *)

(** 共同星形的腿若与序数图式的径向过渡及指定顶点运输交换，便等于该图式。 *)

Definition vertex_star_comparison {n : nat} (A : X)
    (v : Ordinal n → X) (s : ∀ j, (@Hom (VertexCat T)) A (v j))
    (F : Functor [Ord n] (VertexCat T)) (a : Ordinal n)
    (e : ∀ j, v j ≈S F j) (c : A ≈S F a)
    (H : ∀ j, T⟦e j⟧Ob ∘ s j ≈ ρ[F; a; j] ∘ T⟦c⟧Ob)
  : VertexDiagramEq T (@StarF (VertexCat T) HC [Ord n] A v s) F.
Proof.
  exists e. intros i j f.
  pose proof (@star_transition_square (VertexCat T) HC _ _ _ _ _ _
    (s i) (s j) ρ[F; a; i] ρ[F; a; j]
    T⟦e i⟧Ob T⟦e j⟧Ob T⟦c⟧Ob (H i) (H j)) as K.
  rewrite ordinal_radial_inv, ordinal_radial_comp in K.
  rewrite <- (ordinal_radial_arrow F f) in K. exact K.
Defined.

(** The common vertex of two face factorizations has specified equality. *)

(** 两种面分解的共同顶点具有指定相等。 *)

Definition horn_vertex_overlap {n : nat} {i j k : Ordinal (S n)}
    (Hj : ¬ j = i) (Hk : ¬ k = i)
    (h : HornS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (S n) i)
    (a b : Ordinal n) (E : δ[n; j] a = δ[n; k] b)
  : (lower (face[i; j; Hj] h) a : X) ≈S lower (face[i; k; Hk] h) b.
Proof.
  assert (K : δ[n; j] ∘ ConstF [Ord 0] (C := [Ord n]) a ≈
      δ[n; k] ∘ ConstF [Ord 0] (C := [Ord n]) b).
  { apply (snd (simplex_eq_iff _ _)). intros [[] | []]. exact E. }
  pose (H := horn_face_overlap Hj Hk h
    (ConstF [Ord 0] (C := [Ord n]) a)
    (ConstF [Ord 0] (C := [Ord n]) b) K).
  exact (fst (vertex_nerve_zero_eq_iff _ _) H).
Defined.

(** Ordered common endpoints compare radial transitions by a common
    one-simplex. No higher-dimensional face is needed. *)

(** 有序共同端点通过一个共同一维单形比较径向过渡，不需要更高维面。 *)

Lemma horn_radial_overlap_ordered {n : nat} {i j k : Ordinal (S n)}
    (Hj : ¬ j = i) (Hk : ¬ k = i)
    (h : HornS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (S n) i)
    (a b c d : Ordinal n)
    (Ea : δ[n; j] a = δ[n; k] b)
    (Ec : δ[n; j] c = δ[n; k] d) (Hac : fin_rank a ≤ fin_rank c)
    (e : (lower (face[i; j; Hj] h) a : X) ≈S lower (face[i; k; Hk] h) b)
    (f : (lower (face[i; j; Hj] h) c : X) ≈S lower (face[i; k; Hk] h) d)
  : T⟦f⟧Ob ∘ ρ[lower (face[i; j; Hj] h); a; c] ≈
      ρ[lower (face[i; k; Hk] h); b; d] ∘ T⟦e⟧Ob.
Proof.
  assert (Hbd : fin_rank b ≤ fin_rank d).
  { apply (@fin_skip_order_reflect (S n) k).
    change (fin_rank (δ[n; k] b) ≤ fin_rank (δ[n; k] d)).
    rewrite <- Ea, <- Ec.
    change (fin_rank (@fin_skip (S n) j a) ≤
      fin_rank (@fin_skip (S n) j c)).
    rewrite !fin_skip_rank.
    apply skip_rank_monotone. exact Hac. }
  pose (U := ⟦@ArrowChain [Ord n] a c
    (@nat_le_of_le (fin_rank a) (fin_rank c) Hac)⟧Ch).
  pose (V := ⟦@ArrowChain [Ord n] b d
    (@nat_le_of_le (fin_rank b) (fin_rank d) Hbd)⟧Ch).
  assert (K : δ[n; j] ∘ U ≈ δ[n; k] ∘ V).
  { apply (snd (simplex_eq_iff _ _)).
    intros [[] | [[] | []]]; [exact Ea | exact Ec]. }
  pose (H := horn_face_overlap Hj Hk h U V K).
  pose proof (vertex_radial_comparison
    (lower (Nᵥ(T)[U]Δ (face[i; j; Hj] h)))
    (lower (Nᵥ(T)[V]Δ (face[i; k; Hk] h))) (lower H)
    fin_first (fin_next fin_first) e f) as L.
  change (T⟦f⟧Ob ∘ ρ[lower (face[i; j; Hj] h) ∘F U;
      fin_first; fin_next fin_first] ≈
    ρ[lower (face[i; k; Hk] h) ∘F V; fin_first; fin_next fin_first] ∘
      T⟦e⟧Ob) in L.
  rewrite !ordinal_radial_precomp in L. exact L.
Defined.

(** Common endpoints compare radial transitions in either order.
    The backward case follows by inversion of the same square. *)

(** 任意顺序的共同端点都可比较径向过渡；逆序情形由同一方块取逆得到。 *)

Lemma horn_radial_overlap {n : nat} {i j k : Ordinal (S n)}
    (Hj : ¬ j = i) (Hk : ¬ k = i)
    (h : HornS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (S n) i)
    (a b c d : Ordinal n)
    (Ea : δ[n; j] a = δ[n; k] b)
    (Ec : δ[n; j] c = δ[n; k] d)
    (e : (lower (face[i; j; Hj] h) a : X) ≈S lower (face[i; k; Hk] h) b)
    (f : (lower (face[i; j; Hj] h) c : X) ≈S lower (face[i; k; Hk] h) d)
  : T⟦f⟧Ob ∘ ρ[lower (face[i; j; Hj] h); a; c] ≈
      ρ[lower (face[i; k; Hk] h); b; d] ∘ T⟦e⟧Ob.
Proof.
  destruct (le_dec (fin_rank a) (fin_rank c)) as [H | H].
  - exact (horn_radial_overlap_ordered Hj Hk h a b c d Ea Ec H e f).
  - assert (K : fin_rank c ≤ fin_rank a) by lia.
    pose proof (groupoid_inverse_square _ _ _ _
      (horn_radial_overlap_ordered Hj Hk h c d a b Ec Ea K f e)) as L.
    rewrite !ordinal_radial_inv in L. exact L.
Defined.

End RadialComparisons.
