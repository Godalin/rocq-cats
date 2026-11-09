From Cats Require Export
  Instance.Set.Simplicial.Vertex.Horn2
  Instance.Set.Simplicial.Matching
  Instance.Set.Simplicial.Vertex.Edge.

Local Open Scope nat_scope.

(** * Reconstructing and Filling Two-Dimensional Horn Maps

    The two retained edges may have different labels for their common
    vertex. Overlap gives specified equality; object transport aligns them
    before applying the existing local filling theory. *)

(** * 二维 horn 映射的重构与填充

    两条保留边可以用不同标签表示共同顶点。交叠给出指定相等；先沿对象运输对齐
    端点，再应用已有局部填充理论。 *)

Section TwoHorns.
Universes u p.
Context {X : SetC} {C : Cat} (T : Functor (EqGpd X) C).

(** A local presentation retains three chosen vertices and the local horn.
    Every local filler realizes a filler of the original entire horn map. *)

(** 局部呈现保留三个选定顶点及局部 horn；其每个局部填充实现为原整个 horn
    映射的填充。 *)

Record Horn2Presentation {i : Ordinal 2}
    (h : HornS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 i)
  :=
  { horn2_vertex0 : X
  ; horn2_vertex1 : X
  ; horn2_vertex2 : X
  ; horn2_local : Horn2S (VertexCat T) horn2_vertex0 horn2_vertex1 horn2_vertex2 i
  ; horn2_presentation
      (q : TriangleS (VertexCat T) horn2_vertex0 horn2_vertex1 horn2_vertex2)
    : is_horn2_filler horn2_local q →
      is_horn_filler h (△₂[T; horn2_vertex0; horn2_vertex1; horn2_vertex2] q)
  }.

Arguments horn2_vertex0 {i h} _.
Arguments horn2_vertex1 {i h} _.
Arguments horn2_vertex2 {i h} _.
Arguments horn2_local {i h} _.
Arguments horn2_presentation {i h} _ _ _.

(** Extract a local presentation from any actual horn map. The same
    endpoint-rebasing operation handles both outer orientations. *)

(** 从任意实际 horn 映射提取局部呈现；同一端点调整操作处理两种外侧方向。 *)

Definition horn2_reconstruct {i : Ordinal 2}
    (h : HornS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 i)
  : Horn2Presentation h.
Proof.
  destruct i as [[] | [[] | [[] | []]]].
  - assert (Jf : ¬ (fin_next (fin_next fin_first) : Ordinal 2) = fin_first)
      by discriminate.
    assert (Jh : ¬ (fin_next fin_first : Ordinal 2) = fin_first)
      by discriminate.
    pose (f := face[fin_first; fin_next (fin_next fin_first); Jf] h).
    pose (k := face[fin_first; fin_next fin_first; Jh] h).
    assert (E : δ[1; fin_next (fin_next fin_first)] ∘
        δ[0; fin_next fin_first] ≈
      δ[1; fin_next fin_first] ∘ δ[0; fin_next fin_first]).
    { apply simplex_eq_of_rank. intros [[] | []]. reflexivity. }
    pose (e := fst (vertex_nerve_zero_eq_iff _ _)
      (horn_face_overlap Jf Jh h _ _ E)).
    unshelve refine ({|horn2_vertex0 := lower f fin_first
            ; horn2_vertex1 := lower f (fin_next fin_first)
            ; horn2_vertex2 := lower k (fin_next fin_first)
            ; horn2_local := _
            ; horn2_presentation := _
            |} : Horn2Presentation (i := fin_first) h).
    1: exact (fmap (lower f) (ordinal_step fin_first),
      T⟦e; fmap (lower k) (ordinal_step fin_first);
        reflexivity (lower k (fin_next fin_first) : X)⟧Ar).
    intros [a b] [Ha Hb]. apply (snd (horn_filler_faces_iff _ _)).
    intros j Hj. destruct j as [[] | [[] | [[] | []]]].
    + destruct (Hj eq_refl).
    + transitivity k.
      * lazymatch goal with |- ?x ≈S ?y =>
          refine (@vertex_edge_rebased_eq X C T x y e
            (reflexivity (lower k (fin_next fin_first) : X)) _)
        end.
        rewrite triangle_face_1. exact Hb.
      * apply horn_face_witness_independent.
    + transitivity f.
      * lazymatch goal with |- ?x ≈S ?y =>
          refine (@vertex_edge_rebased_eq X C T x y
            (reflexivity (lower f fin_first : X))
            (reflexivity (lower f (fin_next fin_first) : X)) _)
        end.
        rewrite triangle_face_2. transitivity (fmap (lower f) (ordinal_step fin_first)).
        -- exact Ha.
        -- symmetry. apply vertex_rebase_id.
      * apply horn_face_witness_independent.
  - assert (Jf : ¬ (fin_next (fin_next fin_first) : Ordinal 2) =
        fin_next fin_first) by discriminate.
    assert (Jg : ¬ (fin_first : Ordinal 2) = fin_next fin_first) by discriminate.
    pose (f := face[fin_next fin_first; fin_next (fin_next fin_first); Jf] h).
    pose (g := face[fin_next fin_first; fin_first; Jg] h).
    assert (E : δ[1; fin_next (fin_next fin_first)] ∘ δ[0; fin_first] ≈
      δ[1; fin_first] ∘ δ[0; fin_next fin_first]).
    { apply simplex_eq_of_rank. intros [[] | []]. reflexivity. }
    pose (e := fst (vertex_nerve_zero_eq_iff _ _)
      (horn_face_overlap Jf Jg h _ _ E)).
    unshelve refine ({|horn2_vertex0 := lower f fin_first
            ; horn2_vertex1 := lower f (fin_next fin_first)
            ; horn2_vertex2 := lower g (fin_next fin_first)
            ; horn2_local := _
            ; horn2_presentation := _
            |} : Horn2Presentation (i := fin_next fin_first) h).
    1: exact (fmap (lower f) (ordinal_step fin_first),
      T⟦e; fmap (lower g) (ordinal_step fin_first);
        reflexivity (lower g (fin_next fin_first) : X)⟧Ar).
    intros [a b] [Ha Hb]. apply (snd (horn_filler_faces_iff _ _)).
    intros j Hj. destruct j as [[] | [[] | [[] | []]]].
    + transitivity g.
      * lazymatch goal with |- ?x ≈S ?y =>
          refine (@vertex_edge_rebased_eq X C T x y e
            (reflexivity (lower g (fin_next fin_first) : X)) _)
        end.
        rewrite triangle_face_0. exact Hb.
      * apply horn_face_witness_independent.
    + destruct (Hj eq_refl).
    + transitivity f.
      * lazymatch goal with |- ?x ≈S ?y =>
          refine (@vertex_edge_rebased_eq X C T x y
            (reflexivity (lower f fin_first : X))
            (reflexivity (lower f (fin_next fin_first) : X)) _)
        end.
        rewrite triangle_face_2. transitivity (fmap (lower f) (ordinal_step fin_first)).
        -- exact Ha.
        -- symmetry. apply vertex_rebase_id.
      * apply horn_face_witness_independent.
  - assert (Jg : ¬ (fin_first : Ordinal 2) = fin_next (fin_next fin_first))
      by discriminate.
    assert (Jh : ¬ (fin_next fin_first : Ordinal 2) =
        fin_next (fin_next fin_first)) by discriminate.
    pose (g := face[fin_next (fin_next fin_first); fin_first; Jg] h).
    pose (k := face[fin_next (fin_next fin_first); fin_next fin_first; Jh] h).
    assert (E : δ[1; fin_first] ∘ δ[0; fin_first] ≈
      δ[1; fin_next fin_first] ∘ δ[0; fin_first]).
    { apply simplex_eq_of_rank. intros [[] | []]. reflexivity. }
    pose (e := fst (vertex_nerve_zero_eq_iff _ _)
      (horn_face_overlap Jg Jh h _ _ E)).
    unshelve refine ({|horn2_vertex0 := lower k fin_first
            ; horn2_vertex1 := lower g fin_first
            ; horn2_vertex2 := lower g (fin_next fin_first)
            ; horn2_local := _
            ; horn2_presentation := _
            |} : Horn2Presentation (i := fin_next (fin_next fin_first)) h).
    1: exact (fmap (lower g) (ordinal_step fin_first),
      T⟦reflexivity (lower k fin_first : X);
        fmap (lower k) (ordinal_step fin_first); e⟧Ar).
    intros [a b] [Ha Hb]. apply (snd (horn_filler_faces_iff _ _)).
    intros j Hj. destruct j as [[] | [[] | [[] | []]]].
    + transitivity g.
      * lazymatch goal with |- ?x ≈S ?y =>
          refine (@vertex_edge_rebased_eq X C T x y
            (reflexivity (lower g fin_first : X))
            (reflexivity (lower g (fin_next fin_first) : X)) _)
        end.
        rewrite triangle_face_0. transitivity (fmap (lower g) (ordinal_step fin_first)).
        -- exact Ha.
        -- symmetry. apply vertex_rebase_id.
      * apply horn_face_witness_independent.
    + transitivity k.
      * lazymatch goal with |- ?x ≈S ?y =>
          refine (@vertex_edge_rebased_eq X C T x y
            (reflexivity (lower k fin_first : X)) e _)
        end.
        rewrite triangle_face_1. exact Hb.
      * apply horn_face_witness_independent.
    + destruct (Hj eq_refl).
Defined.

(** Any chosen local filling structure gives actual horn-map fillers. *)

(** 任意选定局部填充结构均给出实际 horn 映射的填充。 *)

Program Definition vertex_horn2_HasFillers (i : Ordinal 2)
    `{HF : !HasHorn2Fillers (VertexCat T) i}
  : HasHornFillers (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 i
  :=
  {|horn_fill h := _
  |}.
Next Obligation.
  pose (r := horn2_reconstruct h).
  pose (q := @horn2_fill (VertexCat T) i HF
    (horn2_vertex0 r) (horn2_vertex1 r) (horn2_vertex2 r) (horn2_local r)).
  exists (△₂[T; horn2_vertex0 r; horn2_vertex1 r; horn2_vertex2 r] q.1).
  exact (horn2_presentation r q.1 q.2).
Defined.

(** Every category has actual two-dimensional inner horn fillers. *)

(** 每个范畴均具有实际二维内 horn 填充。 *)

Definition vertex_inner_horn2_HasFillers
  : HasHornFillers (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2
      (fin_next fin_first)
  := @vertex_horn2_HasFillers (fin_next fin_first)
      (inner_horn2_HasFillers (VertexCat T)).

(** A groupoid on the selected objects supplies all actual two-dimensional
    horn fillers. The second outer local construction remains the dual one. *)

(** 选定对象上的群胚提供全部实际二维 horn 填充；第二类外侧局部构造仍来自对偶。 *)

Definition vertex_groupoid_horn2_HasFillers
    `{HC : !IsGroupoid (VertexCat T)} (i : Ordinal 2)
  : HasHornFillers (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 i
  := @vertex_horn2_HasFillers i (@horn2_HasFillers (VertexCat T) HC i).

End TwoHorns.

Arguments horn2_vertex0 {_ _} _ {_ _} _.
Arguments horn2_vertex1 {_ _} _ {_ _} _.
Arguments horn2_vertex2 {_ _} _ {_ _} _.
Arguments horn2_local {_ _} _ {_ _} _.
Arguments horn2_presentation {_ _} _ {_ _} _ _ _.
