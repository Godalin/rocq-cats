From Cats.Set.Relation Require Export
  StrongNormalization
  Sum.

(** * Strong Normalization by Quasi-Commutation

    Separate termination of two relations does not imply termination of
    their sum. Quasi-commutation supplies the missing interaction: an
    [S] step followed by an [R] step can be replaced by an [R] step and
    a finite mixed tail. The tail may duplicate or discard residual work.

    The proof below constructs normalization trees directly. It does not
    infer accessibility from the absence of infinite sequences, choose
    successors, enumerate edges or identify their witnesses. *)

(** * 由准交换得到强归一化

    两个关系分别终止，并不蕴含其和终止。准交换补上所需的相互作用：一个
    [S] 步骤后接一个 [R] 步骤，可改为一个 [R] 步骤后接有限混合尾部。
    尾部允许复制或丢弃剩余工作。

    以下证明直接构造归一化树，不从不存在无限序列推断可达性，不选择后继、
    枚举边或识别其见证。 *)

Local Open Scope relation_scope.

(** [R] quasi-commutes over [S]. The first replacement edge must be an
    actual [R] step; an empty replacement would not force progress. The
    mixed tail has its own path bound, independent of normalization trees. *)

(** [R] 在 [S] 上准交换。替换的首边必须是实际的 [R] 步骤；空替换不能保证
    进展。混合尾部有独立的路径界，不依赖归一化树的界。 *)

Definition is_quasi_commuting@{a r t p +} {A : Type@{a}}
    (R : A → A → Type@{r}) (S : A → A → Type@{t})
  : Type
  := ∀ x y z, S x y → R y z →
      ∃ v, R x v ∧ ReflTransClosure@{a _ p} (R ⊕R S) v z.

(** ** Transporting Readiness

    Fix two relations with independent edge sizes, their quasi-commutation
    witness, a path bound [p] and an output tree bound [s]. Component
    trees have independent bounds [sr] and [st]. Readiness means that
    every immediate [R] successor already has a mixed normalization tree.
    Quasi-commutation transports this property along an [S] edge. *)

(** ** 传递就绪性

    固定边大小独立的两个关系、其准交换见证、路径界 [p] 和输出树界 [s]。
    分量树另有独立的界 [sr] 与 [st]。
    就绪性表示每个直接 [R] 后继已有混合归一化树；准交换沿 [S] 边传递
    这一性质。 *)

Section QuasiCommutation.
Universes a r t p s sr st.
Context {A : Type@{a}} {R : A → A → Type@{r}} {S : A → A → Type@{t}}.
Context (commute : is_quasi_commuting@{a r t p _ _} R S).

(** The first replacement edge reaches a ready subtree; the remaining
    finite path selects another subtree, regardless of its witness size. *)

(** 替换首边到达已就绪的子树；剩余有限路径再选取子树，不受其见证大小影响。 *)

Definition quasi_commuting_ready {x y : A} (h : S x y)
    (ready : ∀ v, R x v → SN@{a _ s} (R ⊕R S) v)
  : ∀ z, R y z → SN@{a _ s} (R ⊕R S) z.
Proof.
  intros z k. destruct (commute x y z h k) as [v [first tail]].
  exact (sn_rtc tail (ready v first)).
Defined.

(** An [S] tree handles successive administrative steps. Readiness
    handles [R] steps, and is transported to each [S] child. *)

(** [S] 树处理连续辅助步骤；就绪性处理 [R] 步骤，并传到每个 [S] 子节点。 *)

Definition sn_sum_ready {x : A} (pS : SN@{a t st} S x)
    (ready : ∀ v, R x v → SN@{a _ s} (R ⊕R S) v)
  : SN@{a _ s} (R ⊕R S) x.
Proof.
  revert ready. induction pS as [x next ih]. intros ready.
  apply sn_intro. intros y [h | h].
  - exact (ready y h).
  - exact (ih y h (quasi_commuting_ready h ready)).
Defined.

(** Induction on the [R] tree supplies readiness. Termination of [S]
    is required at every element, while [R] needs only the given root tree.
    Neither component tree is compared with the resulting mixed tree. *)

(** 对 [R] 树归纳提供就绪性。[S] 须在每个元素处终止，而 [R] 只需要给定
    根处的树；不比较任一分量树与结果混合树。 *)

Definition sn_sum_quasi_commuting (normalS : ∀ y, SN@{a t st} S y)
    {x : A} (pR : SN@{a r sr} R x)
  : SN@{a _ s} (R ⊕R S) x.
Proof.
  induction pR as [x next ih].
  exact (sn_sum_ready (normalS x) ih).
Defined.

End QuasiCommutation.
