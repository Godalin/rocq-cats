From Cats Require Export
  Instance.Set.Simplicial.Vertex.Filling.

Local Open Scope nat_scope.

(** * Actual Outer Horns and Invertibility

    Matching descent constructs a horn from its two retained edges before
    any filler is chosen. Filling this horn recovers right division. *)

(** * 实际外 horn 与可逆性

    在选择任何填充之前，匹配下降先从两条保留边构造 horn；填充此 horn 恢复右除法。 *)

Section OuterHorns.
Universes u p.
Context {X : SetC} {C : Cat} (T : Functor (EqGpd X) C).

(** Two arrows with common source agree on every overlap of the two
    retained faces. Mixed overlaps are constant at their shared vertex. *)

(** 同源的两条箭头在两个保留面的全部交叠上相容；不同面的交叠常值于共同顶点。 *)

Program Definition outer_horn2_matching {A B D : X}
    (f : (@Hom (VertexCat T)) A B) (h : (@Hom (VertexCat T)) A D)
  : HornMatchingS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 1 fin_first
  :=
  {|matching_value j := match j.1 with
      | inl _ => △₁[T; A; D] h
      | inr (inl _) => △₁[T; A; D] h
      | inr (inr _) => △₁[T; A; B] f
      end
  |}.
Next Obligation.
  destruct i as [i Hi], j as [j Hj].
  destruct i as [[] | [[] | [[] | []]]];
    destruct j as [[] | [[] | [[] | []]]];
    try (destruct (Hi eq_refl)); try (destruct (Hj eq_refl)).
  - refine {|lower := vertex_ordinal_precomp_eq T f0 h0 _
        (⟦ArrowChain h⟧Ch)
            |}.
    intros z. exact (@fin_skip_injective 2 (fin_next fin_first)
      (f0 z) (h0 z) (fst (simplex_eq_iff _ _) E z)).
  - refine {|lower := vertex_constant_precomp_eq T _ _ f0 h0
        fin_first fin_first _ _ (reflexivity (A : X))
            |}.
    + intros z. pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
      change (δ[1; fin_next fin_first] (f0 z) =
        δ[1; fin_next (fin_next fin_first)] (h0 z)) in Ez.
      destruct (f0 z) as [[] | [[] | []]], (h0 z) as [[] | [[] | []]];
        try reflexivity; discriminate.
    + intros z. pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
      change (δ[1; fin_next fin_first] (f0 z) =
        δ[1; fin_next (fin_next fin_first)] (h0 z)) in Ez.
      destruct (f0 z) as [[] | [[] | []]], (h0 z) as [[] | [[] | []]];
        try reflexivity; discriminate.
  - refine {|lower := vertex_constant_precomp_eq T _ _ f0 h0
        fin_first fin_first _ _ (reflexivity (A : X))
            |}.
    + intros z. pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
      change (δ[1; fin_next (fin_next fin_first)] (f0 z) =
        δ[1; fin_next fin_first] (h0 z)) in Ez.
      destruct (f0 z) as [[] | [[] | []]], (h0 z) as [[] | [[] | []]];
        try reflexivity; discriminate.
    + intros z. pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
      change (δ[1; fin_next (fin_next fin_first)] (f0 z) =
        δ[1; fin_next fin_first] (h0 z)) in Ez.
      destruct (f0 z) as [[] | [[] | []]], (h0 z) as [[] | [[] | []]];
        try reflexivity; discriminate.
  - refine {|lower := vertex_ordinal_precomp_eq T f0 h0 _
        (⟦ArrowChain f⟧Ch)
            |}.
    intros z. exact (@fin_skip_injective 2 (fin_next (fin_next fin_first))
      (f0 z) (h0 z) (fst (simplex_eq_iff _ _) E z)).
Defined.

(** Descent realizes the outer horn without requiring a missing edge. *)

(** 下降实现外 horn，不要求预先给出缺失边。 *)

Definition OuterHorn2N {A B D : X}
    (f : (@Hom (VertexCat T)) A B) (h : (@Hom (VertexCat T)) A D)
  : HornS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 fin_first
  := SieveMatchingN _ _ (outer_horn2_matching f h).

(** The middle retained face recovers the prescribed long edge. *)

(** 中间保留面恢复指定长边。 *)

Lemma outer_horn2_face_1 {A B D : X}
    (f : (@Hom (VertexCat T)) A B) (h : (@Hom (VertexCat T)) A D)
    (H : ¬ (fin_next fin_first : Ordinal 2) = fin_first)
  : face[fin_first; fin_next fin_first; H] (OuterHorn2N f h) ≈S
      △₁[T; A; D] h.
Proof.
  exact (matching_descend_β _ _ (outer_horn2_matching f h)
    (fin_next fin_first; H)).
Defined.

(** The last retained face recovers the prescribed earlier edge. *)

(** 末个保留面恢复指定先行边。 *)

Lemma outer_horn2_face_2 {A B D : X}
    (f : (@Hom (VertexCat T)) A B) (h : (@Hom (VertexCat T)) A D)
    (H : ¬ (fin_next (fin_next fin_first) : Ordinal 2) = fin_first)
  : face[fin_first; fin_next (fin_next fin_first); H] (OuterHorn2N f h) ≈S
      △₁[T; A; B] f.
Proof.
  exact (matching_descend_β _ _ (outer_horn2_matching f h)
    (fin_next (fin_next fin_first); H)).
Defined.

(** Any actual filler gives a fixed-endpoint local filler. Its three
    vertex labels need only be specified equal to the prescribed ones. *)

(** 任意实际填充给出固定端点的局部填充；其三个顶点标签只需与指定标签广集相等。 *)

Definition outer_horn2_normalize {A B D : X}
    (f : (@Hom (VertexCat T)) A B) (h : (@Hom (VertexCat T)) A D)
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2)
    (H : is_horn_filler (OuterHorn2N f h) x)
  : ∃ q : TriangleS (VertexCat T) A B D,
      is_horn2_filler (i := fin_first) (f, h) q.
Proof.
  assert (J1 : ¬ (fin_next fin_first : Ordinal 2) = fin_first)
    by discriminate.
  assert (J2 : ¬ (fin_next (fin_next fin_first) : Ordinal 2) = fin_first)
    by discriminate.
  pose (E := fst (horn_filler_faces_iff _ _) H).
  assert (Ef : △₁[T; A; B] f ≈S d[Nᵥ(T); 1; fin_next (fin_next fin_first)] x).
  { symmetry. transitivity (face[fin_first; _; J2] (OuterHorn2N f h)).
    - exact (E _ J2).
    - apply outer_horn2_face_2. }
  assert (Eh : △₁[T; A; D] h ≈S d[Nᵥ(T); 1; fin_next fin_first] x).
  { symmetry. transitivity (face[fin_first; _; J1] (OuterHorn2N f h)).
    - exact (E _ J1).
    - apply outer_horn2_face_1. }
  destruct Ef as [[ef Hf]], Eh as [[eh Hh]].
  pose (p0 := ef fin_first).
  pose (p1 := ef (fin_next fin_first)).
  pose (p2 := eh (fin_next fin_first)).
  pose (a := fmap (lower x) (ordinal_step fin_first)).
  pose (b := fmap (lower x) (ordinal_step (fin_next fin_first))).
  exists (T⟦p0; a; p1⟧Ar, T⟦p1; b; p2⟧Ar). split.
  - symmetry. apply (vertex_rebase_of_square T p0 p1 f a).
    pose proof (Hf _ _ (ordinal_step fin_first)) as K.
    change (T⟦p1⟧Ob ∘ (id ∘ f) ≈
      fmap (lower x) (fmap δ[1; fin_next (fin_next fin_first)]
        (ordinal_step fin_first)) ∘ T⟦p0⟧Ob) in K.
    rewrite comp_id_l in K. transitivity
      (fmap (lower x) (fmap δ[1; fin_next (fin_next fin_first)]
        (ordinal_step fin_first)) ∘ T⟦p0⟧Ob).
    + exact K.
    + apply comp_proper; [| reflexivity].
      exact (@functor_fmap_proper [Ord 2] (VertexCat T) (lower x)
        fin_first (fin_next fin_first) _ _ tt).
  - transitivity (T⟦p0; b ∘ a; p2⟧Ar).
    + symmetry. exact (vertex_rebase_comp T p0 p1 p2 a b).
    + pose (c := fmap (lower x) (fmap δ[1; fin_next fin_first]
        (ordinal_step fin_first))).
      transitivity T⟦p0; c; p2⟧Ar.
      * apply (@func_proper _ _ (vertex_rebase_resp T p0 p2)).
        unfold a, b, c. rewrite <- functor_comp.
        exact (@functor_fmap_proper [Ord 2] (VertexCat T) (lower x)
          fin_first (fin_next (fin_next fin_first)) _ _ tt).
      * symmetry. apply (vertex_rebase_of_square T p0 p2 h c).
        pose proof (Hh _ _ (ordinal_step fin_first)) as K.
        change (T⟦p2⟧Ob ∘ (id ∘ h) ≈
          c ∘ T⟦eh fin_first⟧Ob) in K.
        rewrite comp_id_l in K. transitivity (c ∘ T⟦eh fin_first⟧Ob).
        -- exact K.
        -- apply comp_proper; [reflexivity |].
           apply vertex_transport_witness_independent.
Defined.

(** Actual first outer fillers supply the local filling structure. *)

(** 实际第一类外填充提供局部填充结构。 *)

Program Definition vertex_outer_horn2_HasLocalFillers
    `{HF : !HasHornFillers
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 fin_first}
  : HasHorn2Fillers (VertexCat T) fin_first
  :=
  {|horn2_fill A B D h := _
  |}.
Next Obligation.
  destruct h as [f h].
  pose (q := @horn_fill _ 2 fin_first HF (OuterHorn2N f h)).
  exact (outer_horn2_normalize f h q.1 q.2).
Defined.

(** A single family of actual outer fillers already implies a groupoid.
    This invokes the general right-division criterion. *)

(** 仅一类实际外填充便蕴涵群胚；证明调用一般右除法判据。 *)

Definition vertex_outer_horn2_IsGroupoid
    `{HF : !HasHornFillers
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 fin_first}
  : VertexCat T ⦂ Gpd
  := @horn2_0_IsGroupoid (VertexCat T) vertex_outer_horn2_HasLocalFillers.

(** The actual first outer two-horn filling structure characterizes the
    groupoid on the selected objects, rather than on an arbitrary ambient C. *)

(** 实际第一类二维外 horn 填充刻画选定对象上的群胚，而非任意的环境 C。 *)

Definition vertex_outer_horn2_groupoid_iff
  : HasHornFillers
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2 fin_first ↔
      VertexCat T ⦂ Gpd.
Proof.
  split.
  - intros H. exact (@vertex_outer_horn2_IsGroupoid H).
  - intros H. exact (@vertex_groupoid_horn2_HasFillers _ _ T H fin_first).
Defined.

(** Chosen Kan filling therefore gives inverses for every selected arrow. *)

(** 因而选定 Kan 填充为每条选定箭头给出逆。 *)

Definition vertex_kan_IsGroupoid
    `{HK : !HasKanFillers
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _})}
  : VertexCat T ⦂ Gpd
  := @vertex_outer_horn2_IsGroupoid (@hasHornFillers _ HK 1 fin_first).

End OuterHorns.
