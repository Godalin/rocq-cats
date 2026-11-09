From Cats Require Export
  Cat.Groupoid.Division
  Instance.Set.Simplicial.Horn
  Instance.Set.Simplicial.Vertex.Spine.
From Cats Require Import
  Cat.Groupoid.Functor
  Instance.Set.Isomorphism
  Instance.Set.Product.

Local Open Scope nat_scope.

(** * Local Two-Dimensional Horns

    Three vertices are fixed. Triangles are represented by their two-arrow
    spines, and a horn records the two retained edges. Equality compares
    only arrow data. Face 0 omits the later edge, face 1 the composite,
    and face 2 the earlier edge. The second outer construction is obtained
    from the first in the opposite category. *)

(** * 局部二维 horn

    固定三个顶点，以两条箭头组成的脊表示三角形，horn 记录保留的两条边。相等只
    比较箭头数据。面 0 缺少后续边，面 1 缺少复合边，面 2 缺少先行边；第二种
    外侧构造由反范畴中的第一种构造得到。 *)

(** The setoid of fixed-vertex triangle spines. *)

(** 固定顶点的三角形脊广集。 *)

Definition TriangleS (C : Cat) (A B D : @Ob C)
  : SetC
  := HomSet A B ×S HomSet B D.

(** The retained edges of a horn, indexed by its missing face. These are
    local fixed-vertex data, before constructing general simplicial horns. *)

(** 按缺失面编号记录 horn 保留的边。这是局部固定顶点数据，先于一般单纯 horn
    对象的构造。 *)

Definition Horn2S (C : Cat) (A B D : @Ob C) (i : Ordinal 2)
  : SetC
  := match i with
  | inl _ => HomSet A B ×S HomSet A D
  | inr (inl _) => TriangleS C A B D
  | inr (inr _) => HomSet B D ×S HomSet A D
  end.

(** Reversing a triangle swaps its spine arrows. *)

(** 反转三角形交换其两条脊箭头。 *)

Program Definition triangle_op_resp {C : Cat} {A B D : @Ob C}
  : TriangleS C A B D →r TriangleS (C^op) D B A
  :=
  {|func p := (snd p, fst p)
  |}.
Next Obligation.
  intros [f g] [f' g'] [H K]. split; assumption.
Defined.

(** Reversal is a setoid isomorphism with the same swap as inverse. *)

(** 反转为广集同构，逆仍为同一交换。 *)

Definition triangle_op_iso {C : Cat} {A B D : @Ob C}
  : TriangleS C A B D ≅[SetCat] TriangleS (C^op) D B A.
Proof.
  exists triangle_op_resp, (@triangle_op_resp (C^op) D B A).
  split; intros [f g]; split; reflexivity.
Defined.

(** Forget the later edge, retaining the earlier edge and composite. *)

(** 忘却后续边，保留先行边和复合边。 *)

Program Definition horn2_0_resp {C : Cat} {A B D : @Ob C}
  : TriangleS C A B D →r Horn2S C A B D fin_first
  :=
  {|func p := (fst p, snd p ∘ fst p)
  |}.
Next Obligation.
  intros [f g] [f' g'] [H K].
  split; [exact H | apply comp_proper; assumption].
Defined.

(** Forget the earlier edge by applying the first outer restriction to the
    reversed triangle. *)

(** 对反转三角形使用第一种外侧限制，得到忘却先行边的限制。 *)

Definition horn2_2_resp {C : Cat} {A B D : @Ob C}
  : TriangleS C A B D →r
      Horn2S C A B D (fin_next (fin_next fin_first))
  := @horn2_0_resp (C^op) D B A ∘r triangle_op_resp.

(** The three local restrictions share one bounded face index. *)

(** 三种局部限制使用同一个有界面索引。 *)

Definition horn2_resp {C : Cat} {A B D : @Ob C} (i : Ordinal 2)
  : TriangleS C A B D →r Horn2S C A B D i
  := match i with
  | inl _ => horn2_0_resp
  | inr (inl _) => id_resp
  | inr (inr _) => horn2_2_resp
  end.

Notation "'ρ₂[' C ';' A ';' B ';' D ';' i ']'" :=
  (@horn2_resp C A B D i) : hom_scope.

(** A filler restricts to the given retained edges. *)

(** 填充限制后得到给定的保留边。 *)

Definition is_horn2_filler {C : Cat} {A B D : @Ob C} {i : Ordinal 2}
    (h : Horn2S C A B D i) (q : TriangleS C A B D)
  : Type
  := ρ₂[C; A; B; D; i] q ≈S h.

(** Chosen local fillers retain a triangle and its restriction witness.
    Uniqueness and functorial choice are not fields of this structure. *)

(** 选定局部填充保留三角形及其限制见证；结构不额外存储唯一性或函子性选择。 *)

Class HasHorn2Fillers (C : Cat) (i : Ordinal 2)
  :=
  { horn2_fill {A B D : @Ob C} (h : Horn2S C A B D i)
    : ∃ q : TriangleS C A B D, is_horn2_filler h q
  }.

(** Inner horns already specify both spine arrows, so restriction is the
    identity isomorphism in every category. *)

(** 内 horn 已给出两条脊箭头，因此任意范畴中的限制都是恒等同构。 *)

Definition inner_horn2_iso {C : Cat} {A B D : @Ob C}
  : TriangleS C A B D ≅[SetCat]
      Horn2S C A B D (fin_next fin_first)
  := iso_refl.

(** Inner fillers are unique without a groupoid assumption. *)

(** 内填充的唯一性不需要群胚假设。 *)

Definition inner_horn2_universal {C : Cat} {A B D : @Ob C}
    (h : Horn2S C A B D (fin_next fin_first))
  : is_unique (R := carrier_equiv (TriangleS C A B D))
      (is_horn2_filler h) h
  := iso_fiber_universal inner_horn2_iso h.

(** Enable the canonical inner fillers explicitly. *)

(** 显式启用典范内填充。 *)

Program Definition inner_horn2_HasFillers (C : Cat)
  : HasHorn2Fillers C (fin_next fin_first)
  :=
  {|horn2_fill A B D h := (h; _)
  |}.
Next Obligation. destruct h as [f g]. split; reflexivity. Defined.

(** In a groupoid, the missing later edge is [h ∘ f⁻¹]. The inverse laws
    and respectfulness follow from the general groupoid theory. *)

(** 群胚中缺失的后续边为 [h ∘ f⁻¹]；互逆律及保持相等来自一般群胚理论。 *)

Definition horn2_0_iso {C : Cat} `{HC : !IsGroupoid C}
    {A B D : @Ob C}
  : TriangleS C A B D ≅[SetCat] Horn2S C A B D fin_first.
Proof.
  unshelve refine (horn2_0_resp; ({|func p :=
      (fst p, snd p ∘ (@groupoid_inv C HC A B (fst p)))
    |}; _)).
  - intros [f a] [f' a'] [H K]. split; [exact H |].
    apply comp_proper; [exact K | apply groupoid_inv_proper; exact H].
  - split; intros [f g]; split; [reflexivity | | reflexivity |].
    + destruct (iso_precomp_universal (groupoid_arrow_iso f) (g ∘ f))
        as [_ Hunique]. symmetry. apply Hunique. reflexivity.
    + destruct (iso_precomp_universal (groupoid_arrow_iso f) g) as [H _].
      exact H.
Defined.

(** The second outer isomorphism is the first on the opposite, preceded
    by triangle reversal. Its inverse fills the missing earlier edge. *)

(** 第二种外侧同构为三角形反转后接反范畴中的第一种同构；其逆补齐先行边。 *)

Definition horn2_2_iso {C : Cat} `{HC : !IsGroupoid C}
    {A B D : @Ob C}
  : TriangleS C A B D ≅[SetCat]
      Horn2S C A B D (fin_next (fin_next fin_first))
  := iso_trans (@triangle_op_iso C A B D)
      (@horn2_0_iso (C^op) (op_IsGroupoid C) D B A).

(** Every local restriction is invertible in a groupoid. *)

(** 群胚中的每种局部限制都可逆。 *)

Definition horn2_iso {C : Cat} `{HC : !IsGroupoid C}
    {A B D : @Ob C} (i : Ordinal 2)
  : TriangleS C A B D ≅[SetCat] Horn2S C A B D i
  := match i with
  | inl _ => horn2_0_iso
  | inr (inl _) => inner_horn2_iso
  | inr (inr _) => horn2_2_iso
  end.

(** All three local fillers are unique in a groupoid. *)

(** 群胚中的三种局部填充均唯一。 *)

Definition horn2_universal {C : Cat} `{HC : !IsGroupoid C}
    {A B D : @Ob C} (i : Ordinal 2) (h : Horn2S C A B D i)
  : is_unique (R := carrier_equiv (TriangleS C A B D))
      (is_horn2_filler h) ((horn2_iso i).2.1 h).
Proof.
  destruct i as [[] | [[] | [[] | []]]].
  - exact (iso_fiber_universal (@horn2_0_iso C HC A B D) h).
  - exact (iso_fiber_universal (@inner_horn2_iso C A B D) h).
  - exact (iso_fiber_universal (@horn2_2_iso C HC A B D) h).
Defined.

(** Chosen fillers are extracted from the inverse restrictions. *)

(** 从限制的逆提取选定填充。 *)

Program Definition horn2_HasFillers (C : Cat) `{HC : !IsGroupoid C}
    (i : Ordinal 2)
  : HasHorn2Fillers C i
  :=
  {|horn2_fill A B D h := ((horn2_iso i).2.1 h; _)
  |}.
Next Obligation.
  destruct (horn2_universal i h) as [H _]. exact H.
Defined.

(** Chosen first outer fillers supply right division. Thus even this one
    family of outer fillers already implies groupoid structure. *)

(** 选定的第一类外填充提供右除法，因此仅这一类外填充就蕴涵群胚结构。 *)

Program Definition horn2_0_IsGroupoid (C : Cat)
    `{HF : !HasHorn2Fillers C fin_first}
  : C ⦂ Gpd
  := @right_division_IsGroupoid C
      {|right_division A B D f h :=
          (snd (@horn2_fill C fin_first HF A B D (f, h)).1; _)
      |}.
Next Obligation.
  pose (q := @horn2_fill C fin_first HF A B D (f, h)).
  transitivity (snd q.1 ∘ fst q.1).
  - apply comp_proper; [reflexivity | symmetry; exact (fst q.2)].
  - exact (snd q.2).
Defined.

(** The second family supplies left division, so has the dual criterion. *)

(** 第二类外填充提供左除法，因此具有对偶判据。 *)

Program Definition horn2_2_IsGroupoid (C : Cat)
    `{HF : !HasHorn2Fillers C (fin_next (fin_next fin_first))}
  : C ⦂ Gpd
  := @left_division_IsGroupoid C
      {|right_division D B A g h :=
          (fst (@horn2_fill C (fin_next (fin_next fin_first)) HF
            A B D (g, h)).1; _)
      |}.
Next Obligation.
  pose (q := @horn2_fill C (fin_next (fin_next fin_first)) HF
    A B D (g, h)).
  change (@comp C A B D g (fst q.1) ≈ h).
  transitivity (@comp C A B D (snd q.1) (fst q.1)).
  - apply comp_proper; [symmetry; exact (fst q.2) | reflexivity].
  - exact (snd q.2).
Defined.

(** The two outer filling structures together characterize groupoids.
    All witnesses remain chosen data in Type. *)

(** 两类外填充结构共同刻画群胚；全部见证均保留为 Type 中的选定数据。 *)

Definition outer_horn2_groupoid_iff (C : Cat)
  : (HasHorn2Fillers C fin_first ∧
      HasHorn2Fillers C (fin_next (fin_next fin_first))) ↔ C ⦂ Gpd.
Proof.
  split.
  - intros [H _]. exact (@horn2_0_IsGroupoid C H).
  - intros H. split; exact (@horn2_HasFillers C H _).
Defined.

(** * Realization in the Vertex Nerve *)

(** * 在顶点 nerve 中实现 *)

(** A fixed-vertex spine determines an actual two-simplex through the
    general spine reconstruction. *)

(** 固定顶点的脊通过一般脊重构确定实际的二维单形。 *)

Program Definition triangle_simplex_resp@{u p +} {X : SetC} {C : Cat}
    (T : Functor (EqGpd X) C) (A B D : X)
  : TriangleS (VertexCat T) A B D →r
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2
  :=
  {|func p := ⟦{|lower := @PairChain (VertexCat T) A B D (fst p) (snd p)
                |}⟧Sp[T; 2]
  |}.
Next Obligation.
  intros [f g] [f' g'] [H K].
  apply (snd (vertex_simplex_eq_steps _ _)).
  exists (λ i, reflexivity ((@PairChain (VertexCat T) A B D f g) i : X)).
  intros i. rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  change (chain_segment (@PairChain (VertexCat T) A B D f g) _ _
      (ordinal_step i) ≈
    chain_segment (@PairChain (VertexCat T) A B D f' g') _ _
      (ordinal_step i)).
  rewrite !chain_segment_step.
  destruct i as [[] | [[] | []]]; assumption.
Defined.

Notation "'△₂[' T ';' A ';' B ';' D ']'" :=
  (triangle_simplex_resp T A B D) : hom_scope.

(** Fixed-vertex triangle equality is exactly equality of its realized
    simplex. Arbitrary reflexive vertex witnesses act as identities. *)

(** 固定顶点三角形相等恰为所实现单形的相等；任意自反顶点见证都作用为恒等。 *)

Lemma triangle_simplex_eq_iff@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (p q : TriangleS (VertexCat T) A B D)
  : p ≈S q ↔
      (△₂[T; A; B; D] : _ →r
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2) p ≈S
      △₂[T; A; B; D] q.
Proof.
  split.
  - intros H. exact (@func_proper _ _ △₂[T; A; B; D] _ _ H).
  - destruct p as [f g], q as [f' g']. intros H.
    destruct (fst (vertex_simplex_eq_steps _ _) H) as [e E].
    assert (K : ∀ i, chain_edge (@PairChain (VertexCat T) A B D f g) i ≈
      chain_edge (@PairChain (VertexCat T) A B D f' g') i).
    { intros i. pose proof (E i) as Hstep.
      rewrite !vertex_transport_id, comp_id_l, comp_id_r in Hstep.
      change (chain_segment (@PairChain (VertexCat T) A B D f g) _ _
          (ordinal_step i) ≈
        chain_segment (@PairChain (VertexCat T) A B D f' g') _ _
          (ordinal_step i)) in Hstep.
      rewrite !chain_segment_step in Hstep. exact Hstep. }
    split; [exact (K fin_first) | exact (K (fin_next fin_first))].
Defined.

(** The first face retains the later spine arrow. *)

(** 首面保留后续脊箭头。 *)

Lemma triangle_face_0@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (p : TriangleS (VertexCat T) A B D)
  : fmap (lower (d[Nᵥ(T); 1; fin_first]
      ((△₂[T; A; B; D] : _ →r
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2) p)))
      (ordinal_step fin_first) ≈ snd p.
Proof. change (id ∘ snd p ≈ snd p). apply comp_id_l. Defined.

(** The middle face is the composite of the two spine arrows. *)

(** 中间面为两条脊箭头的复合。 *)

Lemma triangle_face_1@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (p : TriangleS (VertexCat T) A B D)
  : fmap (lower (d[Nᵥ(T); 1; fin_next fin_first]
      ((△₂[T; A; B; D] : _ →r
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2) p)))
      (ordinal_step fin_first) ≈ snd p ∘ fst p.
Proof. change ((id ∘ snd p) ∘ fst p ≈ snd p ∘ fst p).
  rewrite comp_id_l. reflexivity. Defined.

(** The last face retains the earlier spine arrow. *)

(** 末面保留先行脊箭头。 *)

Lemma triangle_face_2@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (p : TriangleS (VertexCat T) A B D)
  : fmap (lower (d[Nᵥ(T); 1; fin_next (fin_next fin_first)]
      ((△₂[T; A; B; D] : _ →r
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2) p)))
      (ordinal_step fin_first) ≈ fst p.
Proof. change (id ∘ fst p ≈ fst p). apply comp_id_l. Defined.

(** Selected objects of a groupoid inherit groupoid structure through the
    fully faithful induced inclusion. Enable this structure explicitly. *)

(** 群胚的选定对象通过全忠实诱导嵌入继承群胚结构；此结构须显式启用。 *)

Definition VertexCat_IsGroupoid {X : SetC} {C : Cat}
    (T : Functor (EqGpd X) C) `{HC : !IsGroupoid C}
  : VertexCat T ⦂ Gpd
  := @fully_faithful_IsGroupoid (VertexCat T) C (InducedInclusionF X T)
      (induced_inclusion_fully_faithful X T) HC.

(** An actual simplex fills a local horn when it is equal to a realized
    fixed-vertex triangle whose retained edges match the horn. The chosen
    representatives and all comparison witnesses remain explicit. *)

(** 实际单形填充局部 horn，是指它等于一个实现的固定顶点三角形，且该三角形的
    保留边与 horn 相等；选定代表及全部比较见证均显式保留。 *)

Definition is_local_horn2_filler@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X} {i : Ordinal 2}
    (h : Horn2S (VertexCat T) A B D i)
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2)
  : Type
  := ∃ q : TriangleS (VertexCat T) A B D,
      (△₂[T; A; B; D] q ≈S x) ∧ is_horn2_filler h q.

(** In a groupoid, local filling is a respectful map obtained by inverse
    restriction followed by triangle realization. *)

(** 群胚中的局部填充是保相等映射，由限制的逆后接三角形实现得到。 *)

Definition local_horn2_resp@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} `{HC : !IsGroupoid (VertexCat T)}
    {A B D : X} (i : Ordinal 2)
  : Horn2S (VertexCat T) A B D i →r
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2
  := △₂[T; A; B; D] ∘r (horn2_iso i).2.1.

Notation "'fill₂[' T ';' A ';' B ';' D ';' i ']'" :=
  (@local_horn2_resp _ _ T _ A B D i) : hom_scope.

(** Every inner local horn has a unique realized simplex, in every
    category. This is the image of the identity restriction's unique fiber. *)

(** 任意范畴的每个局部内 horn 都具有唯一实现单形，它是恒等限制的唯一纤维之像。 *)

Definition local_inner_horn2_universal@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (h : Horn2S (VertexCat T) A B D (fin_next fin_first))
  : is_unique (R := carrier_equiv
      ((Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2))
      (is_local_horn2_filler h) (△₂[T; A; B; D] h)
  := iso_fiber_image_universal inner_horn2_iso △₂[T; A; B; D] h.

(** Every local horn in a groupoid has a unique realized simplex. The
    theorem applies the general unique-fiber image construction uniformly. *)

(** 群胚中的每个局部 horn 均具有唯一实现单形；定理统一使用一般唯一纤维像构造。 *)

Definition local_horn2_universal@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} `{HC : !IsGroupoid (VertexCat T)}
    {A B D : X} (i : Ordinal 2) (h : Horn2S (VertexCat T) A B D i)
  : is_unique (R := carrier_equiv
      ((Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2))
      (is_local_horn2_filler h)
      (△₂[T; A; B; D] ((horn2_iso i).2.1 h)).
Proof.
  destruct i as [[] | [[] | [[] | []]]].
  - exact (iso_fiber_image_universal
      (@horn2_0_iso (VertexCat T) HC A B D) △₂[T; A; B; D] h).
  - exact (iso_fiber_image_universal
      (@inner_horn2_iso (VertexCat T) A B D) △₂[T; A; B; D] h).
  - exact (iso_fiber_image_universal
      (@horn2_2_iso (VertexCat T) HC A B D) △₂[T; A; B; D] h).
Defined.

(** Equality of a triangle face follows from equality of its sole edge.
    The two endpoint labels are fixed, and reflexive transports are identities. *)

(** 实现三角形的面只有一条边，其相等蕴含整个面的相等；两个端点标签固定，
    自反运输作用为恒等。 *)

Lemma triangle_face_edge_eq@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (p q : TriangleS (VertexCat T) A B D) (j : Ordinal 2)
    (H : fmap (lower (d[Nᵥ(T); 1; j]
      ((△₂[T; A; B; D] : _ →r
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2) p)))
        (ordinal_step fin_first) ≈
      fmap (lower (d[Nᵥ(T); 1; j] (△₂[T; A; B; D] q)))
        (ordinal_step fin_first))
  : d[Nᵥ(T); 1; j] (△₂[T; A; B; D] p) ≈S
      d[Nᵥ(T); 1; j] (△₂[T; A; B; D] q).
Proof.
  apply (snd (vertex_simplex_eq_steps _ _)).
  exists (λ k, reflexivity (lower (d[Nᵥ(T); 1; j]
    (△₂[T; A; B; D] p)) k : X)).
  intros [[] | []]. rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  exact H.
Defined.

(** Equal local horn restrictions give equal retained one-dimensional faces.
    This uses the specified vertex equality and requires no groupoid. *)

(** 相等的局部 horn 限制给出相等的保留一维面；使用指定顶点相等，不要求群胚。 *)

Lemma triangle_retained_face_eq@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (p q : TriangleS (VertexCat T) A B D) (i j : Ordinal 2)
    (Hj : ¬ j = i) (H : ρ₂[VertexCat T; A; B; D; i] p ≈S
      ρ₂[VertexCat T; A; B; D; i] q)
  : d[Nᵥ(T); 1; j]
      ((△₂[T; A; B; D] : _ →r
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2) p) ≈S
      d[Nᵥ(T); 1; j] (△₂[T; A; B; D] q).
Proof.
  destruct p as [f g], q as [f' g'].
  apply (triangle_face_edge_eq (f, g) (f', g') j).
  destruct i as [[] | [[] | [[] | []]]];
    destruct j as [[] | [[] | [[] | []]]];
    try (destruct (Hj eq_refl)).
  - rewrite !triangle_face_1. exact (snd H).
  - rewrite !triangle_face_2. exact (fst H).
  - rewrite !triangle_face_0. exact (snd H).
  - rewrite !triangle_face_2. exact (fst H).
  - rewrite !triangle_face_0. exact (fst H).
  - rewrite !triangle_face_1. exact (snd H).
Defined.

(** Local equality of the retained edges implies equality of the entire maps
    from the actual horn. The general generator criterion propagates the
    face equations to every degree and every factorization. *)

(** 保留边的局部相等蕴含从实际 horn 出发的整个映射相等；一般生成元判等将面方程
    传播到每个维度及每种分解。 *)

Lemma triangle_horn_restrict_eq@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B D : X}
    (p q : TriangleS (VertexCat T) A B D) (i : Ordinal 2)
    (H : ρ₂[VertexCat T; A; B; D; i] p ≈S
      ρ₂[VertexCat T; A; B; D; i] q)
  : ((△₂[T; A; B; D] : _ →r
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2) p)↾Λ[Nᵥ(T); 2; i]
      ≈N (△₂[T; A; B; D] q)↾Λ[Nᵥ(T); 2; i].
Proof.
  apply (snd (@generated_sieve_map_eq Δ 2
    (∃ j : Ordinal 2, ¬ j = i) (λ _, 1) (λ j, δ[1; j.1])
    (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) _ _)).
  intros [j Hj]. exact (triangle_retained_face_eq p q i j Hj H).
Defined.
