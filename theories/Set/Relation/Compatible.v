From Cats.Set.Relation Require Export Family.

(** * Closure under Single-Hole Operations

    An operation has one varying input. Other arguments can be stored in
    its label. Iteration forms a context around one generating edge; it
    does not change two arguments simultaneously. The operation can change
    the index, as a binder changes the context of a typed term.

    A single carrier is the special case of a constant family over [unit].

    No equations between labels are needed. Indices are raw types: there
    is no implicit transport along an equality of indices. A later client
    must supply any desired transport as an explicit operation. *)

(** * 单孔操作下的闭包

    每个操作只有一个变化的输入，其他参数可以存入其标签。迭代在一条生成边
    周围形成上下文，不会同时改变两个参数。操作可以改变索引，例如绑定构造器
    改变带类型项的上下文。

    单一载体是以 [unit] 为索引的常值族这一特例。

    不需要标签之间的方程。索引是原始类型，不沿索引相等作隐含运输；后续
    客户端须将所需运输显式给成操作。 *)

Local Open Scope relation_scope.

(** A labeled family of unary operations between specified fibers. *)

(** 指定纤维之间带标签的一元操作族。 *)

Class ContextSystem@{i a o +} {I : Type@{i}} (A : I → Type@{a})
  :=
  {
  (** Labels specify the source and target indices. They can retain fixed
      arguments, with a size independent of the carrier universe. *)

  (** 标签指定源、目标索引，可以保存固定参数，其大小独立于载体宇宙。 *)

    context_operation : I → I → Type@{o}

  (** The unique function view applies a labeled operation to its input. *)

  (** 唯一的函数视图将带标签的操作应用于输入。 *)

  ; context_action :> ∀ i j, context_operation i j → A i → A j
  }.

Arguments context_operation {_ _} _ _ _.
Arguments context_action {_ _} _ _ _ _ _.

(** Compatibility means preservation of the relation by each one-hole
    operation. It makes no claim about replacing fixed label data. *)

(** 相容性表示每个单孔操作保持关系，不断言可以替换固定的标签数据。 *)

Definition is_compatible {I : Type} {A : I → Type}
    (K : ContextSystem A) (R : RelationFamily A)
  : Type
  := ∀ i j (c : context_operation K i j) x y,
      R i x y → R j (K i j c x) (K i j c y).

(** A finite context contains exactly one original relation witness.
    Unlike path composition, context iteration introduces no extra redex.
    Its result universe must contain indices, labels, elements and edges. *)

(** 有限上下文恰好包含一个原关系见证。与路径连接不同，上下文迭代不引入
    额外的可归约位置。结果宇宙须容纳索引、标签、元素与边。 *)

Inductive ContextClosure {I : Type} {A : I → Type}
    (K : ContextSystem A) (R : RelationFamily A)
  : RelationFamily A
  :=| context_step {i} {x y : A i}
        : R i x y → ContextClosure K R i x y
    | context_lift {i j} (c : context_operation K i j) {x y : A i}
        : ContextClosure K R i x y →
          ContextClosure K R j (K i j c x) (K i j c y).

Arguments context_step {_ _ _ _ _ _ _} _.
Arguments context_lift {_ _ _ _ _ _} _ {_ _} _.
Notation "R '^C[' K ']'" := (ContextClosure K R)
  (at level 1) : relation_scope.

(** Context iteration itself is compatible, by adding an outer operation. *)

(** 上下文迭代本身相容，只须增加一个外层操作。 *)

Definition context_closure_compatible {I : Type} {A : I → Type}
    (K : ContextSystem A) (R : RelationFamily A)
  : is_compatible K (R^C[K])
  := λ i j c x y p, context_lift c p.

(** Fold contexts into any compatible target receiving the generators. *)

(** 将上下文折叠到接收生成元的任意相容目标。 *)

Definition context_closure_preserves {I : Type} {A : I → Type}
    (K : ContextSystem A) {R S : RelationFamily A}
    (hs : is_compatible K S) (h : R ⊆ᵢ S)
  : R^C[K] ⊆ᵢ S.
Proof.
  intros i x y p. induction p as [i x y p | i j c x y p ih].
  - exact (h i x y p).
  - exact (hs i j c x y ih).
Defined.

(** Inclusions act on the unique generating witness of each context. *)

(** 包含作用于每个上下文中唯一的生成见证。 *)

Definition context_closure_map {I : Type} {A : I → Type}
    (K : ContextSystem A) {R S : RelationFamily A} (h : R ⊆ᵢ S)
  : R^C[K] ⊆ᵢ S^C[K]
  := context_closure_preserves K (context_closure_compatible K S)
      (λ i x y p, context_step (h i x y p)).

(** Context iteration is the least compatible relation containing its
    generators. The two maps do not identify context derivations. *)

(** 上下文迭代是包含生成元的最小相容关系。两个映射不识别上下文推导。 *)

Definition context_closure_universal {I : Type} {A : I → Type}
    (K : ContextSystem A) (R S : RelationFamily A)
    (hs : is_compatible K S)
  : R^C[K] ⊆ᵢ S ↔ R ⊆ᵢ S
  := ((λ h i x y p, h i x y (context_step p)),
      context_closure_preserves K hs).

(** Package context iteration using the generic universal-extension
    constructor. The common witness bound must contain the stored context
    data; the raw construction can instead use a larger result bound. *)

(** 用一般泛扩张构造封装上下文迭代。共同见证界须容纳所存上下文数据；原始
    构造则可以另用更大的结果界。 *)

Definition CompatibleClosure {I : Type} {A : I → Type}
    (K : ContextSystem A)
  : Closure (@RelationFamilyLe I A).
Proof.
  refine (@ClosureFromUniversal (RelationFamily A)
    (@RelationFamilyLe I A) (RelationFamilyPreorder A)
    (is_compatible K) (ContextClosure K) _).
  intros R. split.
  - exact (context_closure_compatible K R).
  - split.
    + intros i x y p. exact (context_step p).
    + intros S hs h. exact (snd (context_closure_universal K R S hs) h).
Defined.

(** Closed relations are precisely compatible ones: collapse a lifted
    generating edge, or fold a context into the compatible relation. *)

(** 闭关系恰好是相容关系：压平提升后的生成边，或将上下文折叠到相容关系。 *)

Definition compatible_closure_closed {I : Type} {A : I → Type}
    (K : ContextSystem A) (R : RelationFamily A)
  : is_closed (CompatibleClosure K) R ↔ is_compatible K R.
Proof.
  split.
  - intros h i j c x y p.
    exact (h j (K i j c x) (K i j c y)
      (context_lift c (context_step p))).
  - intros hs. exact (snd (context_closure_universal K R R hs)
      (λ i, relation_incl_id (R i))).
Defined.

(** Changing generators by their specified equivalence changes context
    closure by the same pointwise equivalence. *)

(** 按指定等价替换生成元，使上下文闭包按同样的逐点等价变化。 *)

Global Instance ContextClosure_proper {I : Type} {A : I → Type}
    (K : ContextSystem A)
  : Proper (RelationFamilyEq ==> RelationFamilyEq) (ContextClosure K).
Proof.
  intros R S h. apply relation_family_equiv_of_inclusions.
  - exact (context_closure_map K (λ i, relation_equiv_forward (h i))).
  - exact (context_closure_map K (λ i, relation_equiv_backward (h i))).
Defined.
