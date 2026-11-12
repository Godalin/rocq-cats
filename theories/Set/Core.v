From Cats Require Export Meta.

(** * Sets with Specified Equality

    [SetC] is the library's standard notion of a mathematical set. It is
    represented by a carrier and a Type-valued equivalence relation, a
    setoid. Whenever a construction speaks of elements being equal, its
    strict equations use this specified relation.

    The carrier supplies representations; the relation specifies when they
    represent the same mathematical element. Distinct representations may
    therefore be equal in the set. We retain representatives and relation
    witnesses, without forming a quotient type or assuming quotient axioms.
    Every operation on the set must respect its specified equality.

    Rocq's [eq] is one possible relation, as in a concrete natural-number
    set. There is no universal requirement that set equality be native
    equality. Relations may take values in [Type], and their witnesses need
    not have the same universe size as carrier elements. *)

(** * 带指定相等的集合

    [SetC] 是本库默认使用的数学集合，表示为载体及 Type 值等价关系，即广集。
    构造中所说的元素相等，以及相应的严格方程，都使用这个指定关系。

    载体提供表示，指定关系说明哪些表示对应同一个数学元素。因此，不同的表示
    可以在集合中相等。我们保留代表与关系见证，不构造商类型，也不假定商公理；
    集合上的每个运算都必须保持其指定相等。

    Rocq 的 [eq] 是一种可选关系，例如具体自然数集合可以采用它；本库不要求
    集合相等普遍采用原生相等。关系可以取值于 [Type]，相等见证的宇宙大小也
    不必与载体元素相同。 *)

Declare Scope set_scope.
Delimit Scope set_scope with set.
Open Scope set_scope.

(** The three fields make the equality policy explicit:
    - [carrier] is the type of representatives, also exposed by coercion
      so that [x : X] can mean [x : carrier X].
    - [carrier_equiv] is the specified equality between representatives.
    - [carrier_setoid] supplies reflexivity, symmetry and transitivity.

    The equivalence laws must be provided when constructing a set; they are
    not new axioms. Their witnesses remain available, and no condition says
    that all witnesses of a given equality are themselves equal.

    In [SetC@{u p}], [u] measures the carrier and [p] the equality witnesses.
    Neither [u <= p] nor [p <= u] is required by this interface. Keeping them
    independent is important when later constructions store equality evidence
    as data or use hom-sets at a different size. *)

(** 三个字段显式给出集合的相等约定：
    - [carrier] 是代表的类型，并通过强制转换使 [x : X] 可以表示
      [x : carrier X]。
    - [carrier_equiv] 是代表之间指定的相等。
    - [carrier_setoid] 提供自反、对称与传递律。

    构造集合时必须提供这些等价律，它们不是新公理。关系见证仍可使用，接口不
    要求同一相等的全部见证本身相等。

    在 [SetC@{u p}] 中，[u] 表示载体层级，[p] 表示相等见证层级；接口既不要求
    [u <= p]，也不要求 [p <= u]。后续构造可能把相等证据存为数据，或使用其他
    大小的 Hom 广集，因此须保留两者的独立性。 *)

Reserved Notation "[≈S]".

Record SetC
  :=
  { carrier :> Type
  ; carrier_equiv : crelation carrier
    where "[≈S]" := carrier_equiv
  ; carrier_setoid :: Equivalence [≈S]
  }.

(** [x ≈S y] reads the equality from the ambient set, and [[≈S]] exposes
    the relation itself when an operation such as [Proper] needs it.
    Setoid rewriting uses this relation together with preservation proofs.

    An arbitrary specified equality does not by itself transport elements
    of every dependent family. Such transport and its coherence are extra
    structure supplied by the later family interfaces. *)

(** [x ≈S y] 从所在广集中读取相等，[[≈S]] 则在 [Proper] 等需要关系参数的
    位置表示关系本身。广集重写同时使用这个关系与运算的保相等证明。

    任意指定相等本身并不会自动给出所有依赖族中的运输；相应的运输及其相干性
    是后面的集合族接口须另外提供的结构。 *)

Notation "[≈S]" := (carrier_equiv _).

Infix "≈S" := (carrier_equiv _)
  (at level 50) : set_scope.

(** Explicit wrappers raise carrier and equality-witness levels separately.
    [LiftT] stores an [A] inside a target universe large enough to contain
    it, and [lower] projects the stored value. This is an explicit wrapper,
    not a principle that arbitrary large types can be resized downward. *)

(** 显式包装用于分别提升载体与相等见证的层级。[LiftT] 将 [A] 存入足以容纳它
    的目标宇宙，[lower] 投影出已保存的值。这是显式包装，不是将任意大类型向下
    重设大小的原理。 *)

Record LiftT@{u v} (A : Type@{u})
  : Type@{v}
  :=
  { lower : A }.
Arguments lower {_} _.

(** Lift the carrier of [X] and its equality witnesses independently.
    Elements are wrappers around old elements; equality is a wrapper around
    the old specified equality. The equivalence laws are obtained by
    unwrapping witnesses, applying the old law and wrapping its result.
    Thus lifting preserves the equality policy and keeps these operations
    computational, within the inferred universe bounds. *)

(** 独立提升 [X] 的载体与相等见证。元素是原元素的包装，相等是原指定相等的
    包装；等价律通过拆开见证、应用原定律、再包装结果得到。因此，在推导出的
    宇宙约束内，提升保留相等约定，并保持这些运算可计算。 *)

Program Definition LiftS@{u p v q +} (X : SetC@{u p})
  : SetC@{v q}
  :=
  {|carrier := LiftT@{u v} X
  ; carrier_equiv x y := LiftT@{p q} (lower x ≈S lower y)
  |}.
Next Obligation.
  split.
  - intros [x]. exact {|lower := reflexivity x
                      |}.
  - intros [x] [y] [H]. exact {|lower := symmetry H
                              |}.
  - intros [x] [y] [z] [H] [K]. exact {|lower := transitivity H K
                                      |}.
Defined.

Notation "'↑S' X" := (LiftS X) (at level 35) : set_scope.
