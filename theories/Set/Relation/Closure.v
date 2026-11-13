From Cats.Set.Relation Require Export Core.
From Cats.Set.Closure Require Export Composition.

(** * Symmetric and Reflexive Transitive Closures

    Symmetric closure records an original edge or a reversed edge. A
    reflexive transitive witness is a finite list of composable edges,
    retaining intermediate elements. Its universe must contain those
    elements and the original witnesses; these bounds need not be equal.

    The chosen closure operators act on relations at one common witness
    bound. For reflexive transitive closure that bound must contain the
    carrier. The raw path construction can instead use a larger result
    universe when the generating relation has small witnesses. *)

(** * 对称闭包与反身传递闭包

    对称闭包记录原始边或反向边；反身传递见证是有限的可复合边列，保留中间
    元素。其宇宙须容纳这些元素及原始见证，但这些界不必相等。

    选定闭包算子作用于共同见证界内的关系。对反身传递闭包，此界须容纳载体；
    若生成关系的见证较小，原始路径构造可以另用较大的结果宇宙。 *)

Local Open Scope relation_scope.

(** One edge with its orientation. No intermediate carrier element is
    stored, so its witness bound can remain below the carrier bound. *)

(** 一条带方向的边。不存储中间载体元素，因此见证界可以保持低于载体界。 *)

Definition SymClosure@{a r} {A : Type@{a}} (R : A → A → Type@{r})
  : A → A → Type@{r}
  := λ x y, (R x y + R y x)%type.

Notation "R '^±'" := (SymClosure R) (at level 1) : relation_scope.

(** Reversing an oriented edge swaps the two alternatives. *)

(** 反转有向边时交换两个分支。 *)

Global Instance SymClosure_Symmetric {A : Type} (R : crelation A)
  : Symmetric (R^±).
Proof. intros x y [h | h]; [exact (inr h) | exact (inl h)]. Defined.

(** Map generators into a symmetric target, using its symmetry witness for
    backward edges. Neither map equality nor proof irrelevance is used. *)

(** 将生成元映入对称目标，反向边使用目标的对称见证。不使用映射相等或证明
    无关性。 *)

Definition sym_closure_preserves {A B : Type}
    {R : crelation A} {S : crelation B} `{HS : !Symmetric S}
    (f : A → B) (h : ∀ x y, R x y → S (f x) (f y))
    {x y : A} (p : R^± x y)
  : S (f x) (f y).
Proof. destruct p as [p | p]; [exact (h _ _ p) | exact (HS _ _ (h _ _ p))].
Defined.

(** An inclusion maps each orientation without changing its endpoints. *)

(** 包含逐方向映射见证，不改变端点。 *)

Definition sym_closure_map {A : Type} {R S : crelation A} (h : R ⊆R S)
  : R^± ⊆R S^±
  := λ x y p, sym_closure_preserves (λ x, x)
      (λ x y q, inl (@h x y q)) p.

(** The least symmetric extension, expressed by two witness transformers. *)

(** 最小对称扩张，以两个见证转换表达。 *)

Definition sym_closure_universal {A : Type} (R S : crelation A)
    `{HS : !Symmetric S}
  : R^± ⊆R S ↔ R ⊆R S
  := ((λ h x y p, @h x y (inl p)),
      (λ h x y p, sym_closure_preserves (λ x, x) (λ x y, @h x y) p)).

(** Empty paths and a generating edge followed by a path. Each nonempty
    witness changes only one edge at its head; concatenation is derived. *)

(** 空路径，或一条生成边接上一条路径。每个非空见证的头部只增加一条边，
    路径连接另行导出。 *)

Inductive ReflTransClosure@{a r p} {A : Type@{a}}
    (R : A → A → Type@{r})
  : A → A → Type@{p}
  :=| rtc_refl (x : A) : ReflTransClosure R x x
    | rtc_cons {x y z : A}
        : R x y → ReflTransClosure R y z → ReflTransClosure R x z.

Arguments rtc_refl {_ _} _.
Arguments rtc_cons {_ _ _ _ _} _ _.

(** Share the established precedence of categorical precomposition so
    relation and category modules can be imported together. *)

(** 与范畴预合成共用已有的优先级，使关系与范畴模块能够同时导入。 *)

Local Set Warnings "-postfix-notation-not-level-1".
Notation "R '^*'" := (ReflTransClosure R) (at level 35) : relation_scope.
Local Set Warnings "+postfix-notation-not-level-1".

(** A single edge is a path with an empty tail. *)

(** 单条边就是尾部为空的路径。 *)

Definition rtc_step {A : Type} {R : crelation A} {x y : A} (p : R x y)
  : (R^*) x y
  := rtc_cons p (rtc_refl y).

(** Concatenation traverses the first path and retains the second as its
    new tail. Its witness remains transparent. *)

(** 连接遍历第一条路径，将第二条保留为新尾部；见证保持透明。 *)

Definition rtc_trans {A : Type} {R : crelation A} {x y z : A}
    (p : (R^*) x y) (q : (R^*) y z)
  : (R^*) x z.
Proof.
  induction p as [x | x y w h p ih].
  - exact q.
  - exact (rtc_cons h (ih q)).
Defined.

(** Empty paths and concatenation form a transparent preorder. This is a
    property of the generated relation, not a global choice of model data. *)

(** 空路径与连接给出透明预序。这是生成关系的性质，不是全局选定的模型数据。 *)

Global Program Instance ReflTransClosure_PreOrder {A : Type}
    (R : crelation A)
  : PreOrder (R^*)
  :=
  {|PreOrder_Reflexive := rtc_refl
  ; PreOrder_Transitive x y z := rtc_trans
  |}.

(** Fold a finite path into any preorder receiving its generating edges.
    This is the reusable induction principle behind leastness and mapping. *)

(** 将有限路径折叠到接收其生成边的任意预序。这是最小性与映射所复用的归纳
    原理。 *)

Definition rtc_preserves {A B : Type} {R : crelation A} {S : crelation B}
    `{HS : !PreOrder S} (f : A → B)
    (h : ∀ x y, R x y → S (f x) (f y))
    {x y : A} (p : (R^*) x y)
  : S (f x) (f y).
Proof.
  induction p as [x | x y z p q ih].
  - reflexivity.
  - exact (transitivity (h _ _ p) ih).
Defined.

(** Map an inclusion by folding into the target path preorder. *)

(** 折叠到目标路径预序，以此映射包含。 *)

Definition rtc_map {A : Type} {R S : crelation A} (h : R ⊆R S)
  : R^* ⊆R S^*
  := λ x y p, rtc_preserves (λ x, x)
      (λ x y q, rtc_step (@h x y q)) p.

(** The least reflexive transitive extension. No relation-function equality
    or identification of path derivations is asserted. *)

(** 最小反身传递扩张，不断言关系函数相等，也不识别路径推导。 *)

Definition rtc_universal {A : Type} (R S : crelation A)
    `{HS : !PreOrder S}
  : R^* ⊆R S ↔ R ⊆R S
  := ((λ h x y p, @h x y (rtc_step p)),
      (λ h x y p, rtc_preserves (λ x, x) (λ x y, @h x y) p)).

(** A symmetric generating relation gives reversible paths. Reversal
    reverses the order of concatenation; it is not a normalization relation. *)

(** 对称生成关系给出可反转的路径。反转倒置连接的次序；它不是正规化关系。 *)

Global Instance ReflTransClosure_Symmetric {A : Type} (R : crelation A)
    `{HS : !Symmetric R}
  : Symmetric (R^*).
Proof.
  intros x y p. induction p as [x | x y z p q ih].
  - exact (rtc_refl x).
  - exact (rtc_trans ih (rtc_step (HS _ _ p))).
Defined.

(** Chosen symmetric closure on the inclusion preorder. The generic
    universal-extension construction supplies its closure laws. *)

(** 包含预序上的选定对称闭包。一般泛扩张构造提供其闭包律。 *)

Definition SymmetricClosure@{a r +} (A : Type@{a})
  : Closure (@subrelation@{a r r} A).
Proof.
  refine (@ClosureFromUniversal (A → A → Type@{r})
    (@subrelation@{a r r} A) (RelationInclusionPreorder A)
    (λ S, Symmetric S) (@SymClosure@{a r} A) _).
  intros R. split.
  - exact (SymClosure_Symmetric R).
  - split.
    + intros x y p. exact (inl p).
    + intros S hs h. exact (snd (sym_closure_universal R S) h).
Defined.

(** Chosen path closure at a common bound containing the carrier and edge
    witnesses. The raw path type above still permits distinct input/output
    witness bounds; only the endomorphism packaging needs this common bound. *)

(** 在容纳载体及边见证的共同界内选定路径闭包。上面的原始路径类型仍允许
    输入、输出见证界不同；只有自映射封装需要这个共同界。 *)

Definition ReflexiveTransitiveClosure@{a r +} (A : Type@{a})
  : Closure (@subrelation@{a r r} A).
Proof.
  refine (@ClosureFromUniversal (A → A → Type@{r})
    (@subrelation@{a r r} A) (RelationInclusionPreorder A)
    (λ S, PreOrder S) (@ReflTransClosure@{a r r} A) _).
  intros R. split.
  - exact (ReflTransClosure_PreOrder R).
  - split.
    + intros x y p. exact (rtc_step p).
    + intros S hs h. exact (snd (rtc_universal R S) h).
Defined.

(** A relation is closed under the symmetric operator exactly when it is
    symmetric. The reverse comparison reverses an original edge by selecting
    the backward alternative; no witness-type equality is needed. *)

(** 关系对对称算子闭合，当且仅当它对称。反向比较选取反向分支，以此反转原始
    边；不需要见证类型相等。 *)

Definition sym_closure_closed {A : Type} (R : crelation A)
  : is_closed (SymmetricClosure A) R ↔ Symmetric R.
Proof.
  split.
  - intros h x y p. exact (h y x (inr p)).
  - intros hs. exact (snd (@sym_closure_universal A R R hs)
      (relation_incl_id R)).
Defined.

(** Closed relations for path closure are precisely preorders. Collapse
    empty paths for reflexivity and two-edge paths for transitivity. *)

(** 路径闭包的闭关系恰好是预序。压平空路径得到反身性，压平两条边的路径得到
    传递性。 *)

Definition rtc_closed@{a r +} {A : Type@{a}} (R : A → A → Type@{r})
  : is_closed (ReflexiveTransitiveClosure@{a r _} A) R ↔ PreOrder R.
Proof.
  split.
  - intros h.
    refine {|PreOrder_Reflexive x := h x x (rtc_refl x)
           ; PreOrder_Transitive x y z p q :=
               h x z (rtc_cons p (rtc_step q))
           |}.
  - intros hs. exact (snd (@rtc_universal A R R hs) (relation_incl_id R)).
Defined.

(** Pointwise equivalent generators give equivalent symmetric closures. *)

(** 逐点等价的生成关系给出等价的对称闭包。 *)

Global Instance SymClosure_proper {A : Type}
  : Proper (relation_equivalence ==> relation_equivalence) (@SymClosure A).
Proof.
  intros R S h. apply relation_equiv_of_inclusions.
  - exact (sym_closure_map (relation_equiv_forward h)).
  - exact (sym_closure_map (relation_equiv_backward h)).
Defined.

(** Path closure also respects the specified relation equivalence. *)

(** 路径闭包也保持指定的关系等价。 *)

Global Instance ReflTransClosure_proper {A : Type}
  : Proper (relation_equivalence ==> relation_equivalence)
      (@ReflTransClosure A).
Proof.
  intros R S h. apply relation_equiv_of_inclusions.
  - exact (rtc_map (relation_equiv_forward h)).
  - exact (rtc_map (relation_equiv_backward h)).
Defined.
