From Cats.Set.Relation Require Export Closure.

(** * Joinability and Confluence

    A peak consists of two reductions with the same source. It is joinable
    when both endpoints reduce to a common successor. A join stores that
    successor and both finite paths; no choice of normal forms is assumed.
    Local confluence concerns two individual steps, whereas confluence
    concerns two arbitrary finite paths. These properties are different
    even though their conclusions have the same form.

    The carrier, edge witnesses and finite paths have separate universe
    parameters. The path bound contains the carrier and edge bounds.
    Native equality below identifies an actual irreducible endpoint of
    this relation; it does not replace any ambient setoid equality. *)

(** * 可汇合性与合流

    分叉由同一来源的两个归约组成。当两个终点都能归约到某个共同后继时，
    称该分叉可汇合。汇合见证保存此后继及两条有限路径，不假定已选定范式。
    局部合流处理两个单步，而合流处理任意两条有限路径；即使结论形状相同，
    这两个性质也不同。

    载体、边见证和有限路径各有独立宇宙参数；路径界容纳载体及边的界。
    下文的原生相等识别此关系的实际不可约终点，不替代环境中的广集相等。 *)

Local Open Scope relation_scope.

(** A common reduct together with the two paths reaching it. The paths
    may be empty, so every element is joinable with itself. *)

(** 共同归约结果及到达它的两条路径。路径可以为空，故每个元素都可与自身汇合。 *)

Definition Join@{a r p} {A : Type@{a}} (R : A → A → Type@{r})
    (x y : A)
  : Type@{p}
  := ∃ z, ReflTransClosure@{a r p} R x z ∧
      ReflTransClosure@{a r p} R y z.

Notation "x '↓[' R ']' y" := (Join R x y)
  (at level 70, R at level 0) : relation_scope.

(** Mixed local peaks may use different rule families; their residual
    paths use an explicitly specified target relation. This does not
    require either family to be locally confluent with itself. *)

(** 混合局部分叉可使用不同规则族，其剩余路径使用显式指定的目标关系。
    这不要求任一规则族自身局部合流。 *)

Definition is_locally_joinable@{a r s t p +} {A : Type@{a}}
    (R : A → A → Type@{r}) (S : A → A → Type@{s})
    (T : A → A → Type@{t})
  : Type
  := ∀ x y z, R x y → S x z → Join@{a t p} T y z.

(** A one-step peak at a fixed source admits a join. *)

(** 固定来源处的任意单步分叉都有汇合见证。 *)

Definition is_locally_confluent_at@{a r p +} {A : Type@{a}}
    (R : A → A → Type@{r}) (x : A)
  : Type
  := ∀ y z, R x y → R x z → Join@{a r p} R y z.

(** Every source has the preceding local property. *)

(** 每个来源都满足上述局部性质。 *)

Definition is_locally_confluent@{a r p +} {A : Type@{a}}
    (R : A → A → Type@{r})
  : Type
  := ∀ x, is_locally_confluent_at@{a r p _} R x.

(** Every pair of finite paths from this source admits a join. *)

(** 从此来源出发的任意两条有限路径都能汇合。 *)

Definition is_confluent_at@{a r p +} {A : Type@{a}}
    (R : A → A → Type@{r}) (x : A)
  : Type
  := ∀ y z, ReflTransClosure@{a r p} R x y →
      ReflTransClosure@{a r p} R x z → Join@{a r p} R y z.

(** Confluence supplies these joins uniformly at every source. *)

(** 合流在每个来源处一致地提供这些汇合见证。 *)

Definition is_confluent@{a r p +} {A : Type@{a}}
    (R : A → A → Type@{r})
  : Type
  := ∀ x, is_confluent_at@{a r p _} R x.

(** Irreducibility rules out every outgoing edge by an empty type. It
    supplies no decision procedure for finding an edge or a reduct. *)

(** 不可约性将每条向外边映到空类型；它不提供寻找边或归约结果的判定过程。 *)

Definition is_irreducible {A : Type} (R : crelation A) (x : A)
  : Type
  := ∀ y, R x y → Empty_set.

(** ** Constructing and Mapping Joins

    Fix a carrier and directed relation. Empty paths, reversal of the two
    legs and prefixing paths give elementary join constructors. Joinability
    is always reflexive and symmetric; it is not generally transitive. *)

(** ** 构造与映射汇合

    固定载体及有向关系。空路径、交换两腿和前接路径给出基本汇合构造。
    可汇合性总是自反且对称，但一般并不传递。 *)

Section Joins.
Context {A : Type} {R : crelation A}.

(** The common reduct is the element itself. *)

(** 以元素自身作为共同归约结果。 *)

Definition join_refl (x : A)
  : x ↓[ R ] x
  := existT _ x (rtc_refl x, rtc_refl x).

(** Exchanging the paths preserves the common reduct. *)

(** 交换路径，保留共同归约结果。 *)

Definition join_sym {x y : A} (h : x ↓[ R ] y)
  : y ↓[ R ] x.
Proof. destruct h as [z [p q]]. exact (existT _ z (q, p)). Defined.

(** Prefix either leg with a path. This operation does not assert
    transitivity of joinability. *)

(** 在任一腿前接一条路径；这并非断言可汇合性的传递性。 *)

Definition join_prefix {x x' y y' : A}
    (p : (R^*) x x') (q : (R^*) y y') (h : x' ↓[ R ] y')
  : x ↓[ R ] y.
Proof.
  destruct h as [z [left right]].
  exact (existT _ z (rtc_trans p left, rtc_trans q right)).
Defined.

(** Confluence at a source is inherited by any of its descendants:
    prefix both paths with the given path from the original source. *)

(** 来源处的合流性由任意后继继承：在两条路径前接上从原来源出发的给定路径。 *)

Definition confluent_at_descendant {x y : A}
    (h : is_confluent_at R x) (p : (R^*) x y)
  : is_confluent_at R y
  := λ u v q s, h u v (rtc_trans p q) (rtc_trans p s).

(** A single step is a finite path, so confluence implies local confluence. *)

(** 单步也是有限路径，因此合流蕴含局部合流。 *)

Definition confluent_locally_confluent (h : is_confluent R)
  : is_locally_confluent R
  := λ x y z p q, h x y z (rtc_step p) (rtc_step q).

End Joins.

(** A map preserving generating steps maps the common successor and both
    paths. No injectivity or equality of edge witnesses is needed. *)

(** 保持生成步骤的映射同时映射共同后继与两条路径，不要求单射或边见证相等。 *)

Definition join_preserves {A B : Type} {R : crelation A} {S : crelation B}
    (f : A → B) (h : ∀ x y, R x y → S (f x) (f y))
    {x y : A} (p : x ↓[ R ] y)
  : f x ↓[ S ] f y.
Proof.
  destruct p as [z [left right]].
  exists (f z). split.
  - exact (rtc_preserves f (λ u v q, rtc_step (h u v q)) left).
  - exact (rtc_preserves f (λ u v q, rtc_step (h u v q)) right).
Defined.

(** Changing edge witnesses by an inclusion changes join witnesses in
    the same direction. This alone does not transfer confluence: the
    larger relation may have additional peaks. *)

(** 包含沿同一方向转换汇合见证。但这本身不能传递合流性，因为较大的关系
    可能具有额外分叉。 *)

Definition join_map {A : Type} {R S : crelation A} (h : R ⊆R S)
    {x y : A} (p : x ↓[ R ] y)
  : x ↓[ S ] y
  := join_preserves (λ x, x) h p.

(** Pointwise equivalent edge relations give equivalent join relations;
    the comparison transforms the stored paths. *)

(** 逐点等价的边关系给出等价的汇合关系；比较转换所存路径。 *)

Global Instance Join_proper {A : Type}
  : Proper (relation_equivalence ==> relation_equivalence) (@Join A).
Proof.
  intros R S h. apply relation_equiv_of_inclusions.
  - exact (λ x y, join_map (relation_equiv_forward h)).
  - exact (λ x y, join_map (relation_equiv_backward h)).
Defined.

(** Equivalent edge presentations have the same confluence property.
    Map the incoming paths backward and their join forward. *)

(** 等价的边呈现具有相同合流性：反向映射传入路径，再正向映射其汇合。 *)

Definition confluent_transport {A : Type} {R S : crelation A}
    (e : R ≈R S) (h : is_confluent R)
  : is_confluent S
  := λ x y z p q, join_map (relation_equiv_forward e)
      (h x y z (rtc_map (relation_equiv_backward e) x y p)
        (rtc_map (relation_equiv_backward e) x z q)).

(** Confluence respects the specified pointwise relation equivalence. *)

(** 合流保持指定的逐点关系等价。 *)

Global Instance is_confluent_proper {A : Type}
  : Proper (relation_equivalence ==> iffT) (@is_confluent A).
Proof.
  intros R S h. split.
  - exact (confluent_transport h).
  - exact (confluent_transport (λ x y,
      (snd (h x y), fst (h x y)))).
Defined.

(** ** Uniqueness of Irreducible Results

    Fix a directed relation and irreducible endpoints. A finite path out
    of an irreducible element must be empty. Consequently a join of two
    such endpoints identifies them by native equality, without deciding
    whether an arbitrary element is irreducible. *)

(** ** 不可约结果的唯一性

    固定有向关系与不可约终点。不可约元素的向外有限路径只能为空，因此两个
    不可约终点的汇合会给出其原生相等；无需判定任意元素是否不可约。 *)

Section IrreducibleResults.
Context {A : Type} {R : crelation A}.

(** An empty path fixes its endpoint; a nonempty path contradicts
    irreducibility at its first edge. *)

(** 空路径固定其终点；非空路径的首边则与不可约性矛盾。 *)

Definition irreducible_rtc {x y : A} (h : is_irreducible R x)
    (p : (R^*) x y)
  : x = y.
Proof.
  destruct p as [x | x z y step tail].
  - reflexivity.
  - exact (match h z step with end).
Defined.

(** Both paths of a join must be empty at irreducible endpoints. *)

(** 不可约终点处，汇合的两条路径都只能为空。 *)

Definition irreducible_join_unique {x y : A}
    (hx : is_irreducible R x) (hy : is_irreducible R y)
    (h : x ↓[ R ] y)
  : x = y.
Proof.
  destruct h as [z [p q]].
  exact (eq_trans (irreducible_rtc hx p) (eq_sym (irreducible_rtc hy q))).
Defined.

(** Confluence at a source suffices for uniqueness of its irreducible
    results. This is a uniqueness theorem, not a search algorithm. *)

(** 来源处的合流足以保证其不可约结果唯一。这是唯一性定理，不是搜索算法。 *)

Definition confluent_irreducible_unique {x y z : A}
    (h : is_confluent_at R x) (p : (R^*) x y) (q : (R^*) x z)
    (hy : is_irreducible R y) (hz : is_irreducible R z)
  : y = z
  := irreducible_join_unique hy hz (h y z p q).

End IrreducibleResults.
