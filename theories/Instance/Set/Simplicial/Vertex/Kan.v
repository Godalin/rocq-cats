From Cats Require Export
  Instance.Set.Simplicial.Vertex.Outer
  Instance.Set.Simplicial.Vertex.Star
  Instance.Set.Simplicial.Vertex.Coskeletal.

Local Open Scope nat_scope.

(** * Kan Filling of a Groupoid Nerve

    All retained faces contain the vertex opposite the omitted face.
    Their radial arrows descend to a common star, uniformly in dimension. *)

(** * 群胚 nerve 的 Kan 填充

    所有保留面都含有缺失面的对顶点；其径向箭头统一下降为共同星形，适用于任意维度。 *)

(** The two-dimensional inner horn from %\coqref{Cats.Instance.Set.Simplicial.Boundary.Horn}
    {%[Horn]%}% asks for a composite;
    an outer horn instead asks to solve for a missing factor. For example,
    given [f : A → B] and [h : A → D], finding [g : B → D] with
    [h ≈ g ∘ f] is possible in a groupoid by composing h with the inverse
    of f. %\coqref{Cats.Instance.Set.Simplicial.Vertex.Horn2.inner horn2 universal}
    {%[inner_horn2_universal]%}% and %\coqref{Cats.Instance.Set.Simplicial.Vertex.Horn2.outer horn2 groupoid iff}
    {%[outer_horn2_groupoid_iff]%}% separate
    these phenomena in dimension two.

    This chapter assumes [IsGroupoid (VertexCat T)] and constructs fillers
    in every positive dimension, not just for the drawn triangles. Its
    higher-dimensional proof uses the overlap machinery from %\coqref{Cats.Instance.Set.Simplicial.Matching}
    {%[Matching]%}%
    and the preceding star construction. These are advanced dependencies;
    the conclusion does not say that every category nerve or every
    simplicial set has Kan fillers. *)

(** %\coqref{Cats.Instance.Set.Simplicial.Boundary.Horn}
    {%[Horn]%}% 中的二维内 horn 要求补出复合；外 horn 则要求解出缺失的因子。
    例如，给定 [f : A → B]、[h : A → D]，需要寻找 [g : B → D] 满足
    [h ≈ g ∘ f]；在群胚中可将 h 与 f 的逆复合得到 g。
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Horn2.inner horn2 universal}
    {%[inner_horn2_universal]%}% 和 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Horn2.outer horn2 groupoid iff}
    {%[outer_horn2_groupoid_iff]%}% 在二维分别刻画
    这两种现象。

    本章假设 [IsGroupoid (VertexCat T)]，构造所有正维的填充，而不只处理
    图上的三角形。高维证明使用 %\coqref{Cats.Instance.Set.Simplicial.Matching}
    {%[Matching]%}% 的交叠机制及前面的星形构造。
    这些属于进阶依赖；结论没有声称任意范畴的 nerve 或任意单纯集合都有 Kan
    填充。 *)

Section HigherHorns.
Universes u p.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C)
    `{HC : !IsGroupoid (VertexCat T)}
    (n : nat) (i : Ordinal (S (S n)))
    (h : HornS (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S (S n)) i).

(** Choose a retained face containing the requested vertex. There are
    at least three vertices, so finite avoidance suffices. *)

(** 选择包含所需顶点的保留面；至少有三个顶点，故有限避开运算足够。 *)

Definition horn_chart (a : Ordinal (S (S n)))
  : ∃ j : Ordinal (S (S n)), (¬ j = i) ∧ (¬ j = a)
  := fin_avoid_pair i a.

(** Locate the vertex inside its chosen chart. *)

(** 定位顶点在其选定图表中的位置。 *)

Definition horn_chart_vertex (a : Ordinal (S (S n)))
  : ∃ b : Ordinal (S n), δ[S n; (horn_chart a).1] b = a
  := @fin_unskip (S (S n)) (horn_chart a).1 a
      (λ E, snd (horn_chart a).2 (eq_sym E)).

(** Every retained chart also contains the common centre i. *)

(** 每个保留图表也都包含共同中心 i。 *)

Definition horn_chart_centre (j : Ordinal (S (S n))) (Hj : ¬ j = i)
  : ∃ b : Ordinal (S n), δ[S n; j] b = i
  := @fin_unskip (S (S n)) j i (λ E, Hj (eq_sym E)).

(** Use one chosen representative for each global vertex label. *)

(** 为每个全局顶点标签使用一个选定代表。 *)

Definition horn_label (a : Ordinal (S (S n)))
  : X
  := lower (face[i; (horn_chart a).1; fst (horn_chart a).2] h)
      (horn_chart_vertex a).1.

(** Overlap compares the chosen label with its occurrence in any face. *)

(** 交叠比较选定标签及其在任意面中的出现。 *)

Definition horn_label_face (j : Ordinal (S (S n))) (Hj : ¬ j = i)
    (b : Ordinal (S n))
  : horn_label (δ[S n; j] b) ≈S lower (face[i; j; Hj] h) b
  := horn_vertex_overlap T (fst (horn_chart (δ[S n; j] b)).2) Hj h
      (horn_chart_vertex (δ[S n; j] b)).1 b
      (horn_chart_vertex (δ[S n; j] b)).2.

(** The common centre label likewise agrees with each chart's centre. *)

(** 共同中心标签同样与每个图表的中心相等。 *)

Definition horn_centre_face (j : Ordinal (S (S n))) (Hj : ¬ j = i)
  : horn_label i ≈S lower (face[i; j; Hj] h) (horn_chart_centre j Hj).1.
Proof.
  apply (horn_vertex_overlap T (fst (horn_chart i).2) Hj h
    (horn_chart_vertex i).1 (horn_chart_centre j Hj).1).
  rewrite (horn_chart_vertex i).2, (horn_chart_centre j Hj).2.
  reflexivity.
Defined.

(** The leg to a vertex follows its chart's radial transition, after
    transporting the common centre into that chart. *)

(** 到一个顶点的腿先将共同中心运输到该图表，再沿图表中的径向过渡行进。 *)

Definition horn_leg (a : Ordinal (S (S n)))
  : (@Hom (VertexCat T)) (horn_label i) (horn_label a)
  := ρ[lower (face[i; (horn_chart a).1; fst (horn_chart a).2] h);
        (horn_chart_centre (horn_chart a).1 (fst (horn_chart a).2)).1;
        (horn_chart_vertex a).1] ∘
      T⟦horn_centre_face (horn_chart a).1 (fst (horn_chart a).2)⟧Ob.

(** Each global leg agrees with its chart's radial leg. Only common
    vertices and one-dimensional overlaps enter this proof. *)

(** 每条全局腿与图表中的径向腿相容；证明仅使用共同顶点及一维交叠。 *)

Lemma horn_leg_face (j : Ordinal (S (S n))) (Hj : ¬ j = i)
    (b : Ordinal (S n))
  : T⟦horn_label_face j Hj b⟧Ob ∘ horn_leg (δ[S n; j] b) ≈
      ρ[lower (face[i; j; Hj] h); (horn_chart_centre j Hj).1; b] ∘
        T⟦horn_centre_face j Hj⟧Ob.
Proof.
  pose (a := δ[S n; j] b).
  pose (k := (horn_chart a).1).
  pose (Hk := fst (horn_chart a).2).
  pose (s := horn_centre_face k Hk).
  pose (t := horn_centre_face j Hj).
  assert (e : (lower (face[i; k; Hk] h) (horn_chart_centre k Hk).1 : X) ≈S
      lower (face[i; j; Hj] h) (horn_chart_centre j Hj).1).
  { transitivity (horn_label i); [symmetry; exact s | exact t]. }
  assert (E : δ[S n; k] (horn_chart_centre k Hk).1 =
      δ[S n; j] (horn_chart_centre j Hj).1).
  { rewrite !(horn_chart_centre _ _).2. reflexivity. }
  pose proof (horn_radial_overlap T Hk Hj h
    (horn_chart_centre k Hk).1 (horn_chart_centre j Hj).1
    (horn_chart_vertex a).1 b E (horn_chart_vertex a).2
    e (horn_label_face j Hj b)) as K.
  unfold horn_leg. change (T⟦horn_label_face j Hj b⟧Ob ∘
    (ρ[lower (face[i; k; Hk] h); (horn_chart_centre k Hk).1;
      (horn_chart_vertex a).1] ∘ T⟦s⟧Ob) ≈
    ρ[lower (face[i; j; Hj] h); (horn_chart_centre j Hj).1; b] ∘ T⟦t⟧Ob).
  pose (r := ρ[lower (face[i; k; Hk] h); (horn_chart_centre k Hk).1;
    (horn_chart_vertex a).1]).
  pose (q := ρ[lower (face[i; j; Hj] h); (horn_chart_centre j Hj).1; b]).
  transitivity ((q ∘ T⟦e⟧Ob) ∘ T⟦s⟧Ob).
  - transitivity ((T⟦horn_label_face j Hj b⟧Ob ∘ r) ∘ T⟦s⟧Ob).
    + symmetry. exact (@comp_assoc (VertexCat T) _ _ _ _ _ _ _).
    + apply comp_proper; [exact K | reflexivity].
  - transitivity (q ∘ (T⟦e⟧Ob ∘ T⟦s⟧Ob)).
    + exact (@comp_assoc (VertexCat T) _ _ _ _ _ _ _).
    + apply comp_proper; [reflexivity |].
      symmetry. exact (vertex_transport_comp T s e t).
Defined.

(** The common star is an actual simplex in the original value universes. *)

(** 共同星形是原值宇宙中的实际单形。 *)

Definition HornStarSimplex
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S (S n))
  := ⟨@StarF (VertexCat T) HC [Ord (S (S n))] (horn_label i) horn_label horn_leg⟩ᵥ.

(** Every retained face of the star recovers the given chart. *)

(** 星形的每个保留面都恢复给定图表。 *)

Lemma horn_star_face (j : Ordinal (S (S n))) (Hj : ¬ j = i)
  : d[Nᵥ(T); S n; j] HornStarSimplex ≈S face[i; j; Hj] h.
Proof.
  refine {|lower := vertex_star_comparison T (horn_label i)
    (λ a, horn_label (δ[S n; j] a)) (λ a, horn_leg (δ[S n; j] a))
    (lower (face[i; j; Hj] h)) (horn_chart_centre j Hj).1
    (horn_label_face j Hj) (horn_centre_face j Hj) (horn_leg_face j Hj)
          |}.
Defined.

(** Generator extensionality upgrades the face equations to filling the
    entire horn map, in every dimension at least two. *)

(** 生成元判等将面方程提升为整个 horn 映射的填充，适用于所有至少二维的情形。 *)

Definition horn_star_filler
  : is_horn_filler h HornStarSimplex.
Proof. apply (snd (horn_filler_faces_iff _ _)). exact horn_star_face. Defined.

(** Any filler identifies every chosen label with the corresponding
    vertex of that filler. Only finite positions use native equality. *)

(** 任意填充将每个选定标签等同于其对应顶点；原生相等仅用于有限位置。 *)

Definition horn_label_filler
    (x : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S (S n)))
    (Hx : is_horn_filler h x) (a : Ordinal (S (S n)))
  : horn_label a ≈S lower x a.
Proof.
  pose (E := fst (horn_filler_faces_iff _ _) Hx
    (horn_chart a).1 (fst (horn_chart a).2)).
  pose proof ((lower E).1 (horn_chart_vertex a).1) as p.
  change ((lower x (δ[S n; (horn_chart a).1] (horn_chart_vertex a).1) : X)
    ≈S horn_label a) in p.
  rewrite (horn_chart_vertex a).2 in p. symmetry. exact p.
Defined.

(** Every filler's radial legs agree with the chosen global legs. *)

(** 任意填充的径向腿都与选定全局腿相容。 *)

Lemma horn_leg_filler
    (x : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S (S n)))
    (Hx : is_horn_filler h x) (a : Ordinal (S (S n)))
  : T⟦horn_label_filler x Hx a⟧Ob ∘ horn_leg a ≈
      ρ[lower x; i; a] ∘ T⟦horn_label_filler x Hx i⟧Ob.
Proof.
  pose (j := (horn_chart a).1).
  pose (Hj := fst (horn_chart a).2).
  pose (c := (horn_chart_centre j Hj).1).
  pose (b := (horn_chart_vertex a).1).
  assert (E : VertexDiagramEq T (lower (face[i; j; Hj] h))
      (lower x ∘F δ[S n; j])).
  { symmetry. exact (lower (fst (horn_filler_faces_iff _ _) Hx j Hj)). }
  assert (K : ∀ (s : (lower (face[i; j; Hj] h) c : X) ≈S
          lower x (δ[S n; j] c))
        (t : (lower (face[i; j; Hj] h) b : X) ≈S lower x (δ[S n; j] b)),
      T⟦t⟧Ob ∘ ρ[lower (face[i; j; Hj] h); c; b] ≈
        ρ[lower x; δ[S n; j] c; δ[S n; j] b] ∘ T⟦s⟧Ob).
  { intros s t.
    pose proof (vertex_radial_comparison T _ _ E c b s t) as L.
    rewrite ordinal_radial_precomp in L. exact L. }
  change (∀ (s : (lower (face[i; j; Hj] h) c : X) ≈S
          lower x (δ[S n; j] (horn_chart_centre j Hj).1))
        (t : (lower (face[i; j; Hj] h) b : X) ≈S
          lower x (δ[S n; j] (horn_chart_vertex a).1)),
      T⟦t⟧Ob ∘ ρ[lower (face[i; j; Hj] h); c; b] ≈
        ρ[lower x; δ[S n; j] (horn_chart_centre j Hj).1;
          δ[S n; j] (horn_chart_vertex a).1] ∘ T⟦s⟧Ob) in K.
  assert (Eb : δ[S n; j] (horn_chart_vertex a).1 = a)
    by exact (horn_chart_vertex a).2.
  rewrite (horn_chart_centre j Hj).2, Eb in K.
  pose (p := horn_centre_face j Hj).
  pose (e := horn_label_filler x Hx i).
  assert (s : (lower (face[i; j; Hj] h) c : X) ≈S lower x i).
  { transitivity (horn_label i); [symmetry; exact p | exact e]. }
  specialize (K s (horn_label_filler x Hx a)).
  pose (r := ρ[lower (face[i; j; Hj] h); c; b]).
  pose (q := ρ[lower x; i; a]).
  transitivity ((q ∘ T⟦s⟧Ob) ∘ T⟦p⟧Ob).
  - transitivity ((T⟦horn_label_filler x Hx a⟧Ob ∘ r) ∘ T⟦p⟧Ob).
    + symmetry. exact (@comp_assoc (VertexCat T) _ _ _ _ _ _ _).
    + apply comp_proper; [exact K | reflexivity].
  - transitivity (q ∘ (T⟦s⟧Ob ∘ T⟦p⟧Ob)).
    + exact (@comp_assoc (VertexCat T) _ _ _ _ _ _ _).
    + apply comp_proper; [reflexivity |].
      symmetry. exact (vertex_transport_comp T p s e).
Defined.

(** In dimensions at least two the star is the unique actual horn filler,
    with respect to the specified simplex equality. *)

(** 在至少二维时，星形是实际 horn 在指定单形相等下的唯一填充。 *)

Definition horn_star_universal
  : is_unique (R := carrier_equiv
      ((Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S (S n))))
      (is_horn_filler h) HornStarSimplex.
Proof.
  refine {|this := horn_star_filler
          ; that := _
          |}.
  intros x Hx. symmetry.
  exact {|lower := vertex_star_comparison T (horn_label i) horn_label horn_leg
    (lower x) i (horn_label_filler x Hx) (horn_label_filler x Hx i)
    (horn_leg_filler x Hx)
         |}.
Defined.

End HigherHorns.

(** ** Kan Fillers for the Vertex Nerve

    Fix a presentation [T : Fct (EqGpd X) C]. Construct one-dimensional
    fillers directly and higher fillers under the additional groupoid
    assumption stated by each construction. *)

(** ** 顶点 nerve 的 Kan 填充

    固定呈现 [T : Fct (EqGpd X) C]，直接构造一维填充，并在各构造声明的额外群胚假设下给出高维填充。 *)

Section KanFilling.
Universes u p.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C).

(** A one-horn specifies one endpoint. The identity edge at that vertex
    fills it, in any category and without choosing any new vertex. *)

(** 一维 horn 指定一个端点；该顶点的恒等边即为填充，不要求群胚，也不选择新顶点。 *)

Definition vertex_horn1_HasFillers (i : Ordinal 1)
  : HasHornFillers (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 1 i.
Proof.
  destruct i as [[] | [[] | []]].
  - assert (J : ¬ (fin_next fin_first : Ordinal 1) = fin_first)
      by discriminate.
    unshelve refine {|horn_fill h :=
        (s[Nᵥ(T); 0; fin_first] (face[fin_first; fin_next fin_first; J] h); _)
                     |}.
    apply (snd (horn_filler_faces_iff _ _)). intros j Hj.
    destruct j as [[] | [[] | []]].
    + destruct (Hj eq_refl).
    + transitivity (face[fin_first; fin_next fin_first; J] h).
      * exact (@simplex_face_degeneracy_next _ 0 fin_first _).
      * apply horn_face_witness_independent.
  - assert (J : ¬ (fin_first : Ordinal 1) = fin_next fin_first)
      by discriminate.
    unshelve refine {|horn_fill h :=
        (s[Nᵥ(T); 0; fin_first] (face[fin_next fin_first; fin_first; J] h); _)
                     |}.
    apply (snd (horn_filler_faces_iff _ _)). intros j Hj.
    destruct j as [[] | [[] | []]].
    + transitivity (face[fin_next fin_first; fin_first; J] h).
      * exact (@simplex_face_degeneracy_id _ 0 fin_first _).
      * apply horn_face_witness_independent.
    + destruct (Hj eq_refl).
Defined.

Context `{HC : !IsGroupoid (VertexCat T)}.

(** The common star supplies chosen fillers uniformly in all dimensions
    at least two. No uniqueness of the choice is stored. *)

(** 共同星形统一提供所有至少二维的选定填充，不额外存储选择的唯一性。 *)

Program Definition vertex_groupoid_higher_HasFillers (n : nat)
    (i : Ordinal (S (S n)))
  : HasHornFillers
      (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S (S n)) i
  :=
  {|horn_fill h := (HornStarSimplex T n i h; horn_star_filler T n i h)
  |}.

(** A groupoid on the selected objects gives all positive-dimensional
    Kan fillers. The construction is explicit and uses no choice axiom. *)

(** 选定对象上的群胚给出全部正维 Kan 填充；构造显式，不使用选择公理。 *)

Program Definition vertex_groupoid_HasKanFillers
  : HasKanFillers (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  :=
  {|hasHornFillers n := match n as d return ∀ i : Ordinal (S d),
        HasHornFillers (Nᵥ(T)) (S d) i with
      | 0 => vertex_horn1_HasFillers
      | S m => vertex_groupoid_higher_HasFillers m
      end
  |}.

End KanFilling.

(** The vertex nerve has chosen Kan filling exactly when its selected
    category is a groupoid. Both directions retain computational witnesses;
    no claim about mere existence or equality of choices is needed. *)

(** 顶点 nerve 具有选定 Kan 填充，当且仅当选定范畴为群胚。双向均保留计算见证，
    不要求仅有存在性，也不比较选择的相等。 *)

Definition vertex_kan_groupoid_iff@{u p +} {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : HasKanFillers (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ↔
      VertexCat T ⦂ Gpd.
Proof.
  split.
  - intros H. exact (@vertex_kan_IsGroupoid _ _ T H).
  - intros H. exact (@vertex_groupoid_HasKanFillers _ _ T H).
Defined.
