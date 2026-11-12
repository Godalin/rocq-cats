(** * Constructive Foundations

    This library develops category theory inside Rocq's type theory. Its
    foundational constructions provide data and proofs without adding
    excluded middle, choice, function extensionality, proof irrelevance or
    uniqueness of identity proofs as axioms. This is the meaning of the
    library's axiom-free aim; Rocq's underlying logic and universe rules
    remain the foundation in which the constructions are checked.

    A mathematical set will be represented by a carrier with a specified
    equivalence relation, called a setoid. That relation is the set's
    equality throughout the library. Operations must preserve it, and their
    laws use it. Rocq's native equality can serve as the specified relation
    of a concrete set, but is not imposed on all sets.

    This module supplies the logical vocabulary used before sets and
    categories are defined. The following modules introduce [SetC], maps
    preserving its equality, and categories whose homs are such sets. *)

(** * 构造性基础

    本库在 Rocq 的类型论内部发展范畴论。基础构造给出数据及证明，不额外引入
    排中律、选择公理、函数外延性、证明无关性或恒等证明唯一性公理。这就是本库
    的无公理主旨：构造仍然在 Rocq 的底层逻辑与宇宙规则中接受检查。

    本库用载体与指定的等价关系表示数学上的集合，称为广集。这个指定关系就是
    全库使用的集合相等，运算须保持它，定律也按它陈述。Rocq 原生相等可以成为
    某个具体集合的指定关系，但不作为所有集合必须采用的相等。

    本模块提供定义集合与范畴之前所需的逻辑语言。后续模块依次介绍广集 [SetC]、
    保持其相等的映射，以及以这种集合为 Hom 的范畴。 *)

(* From Stdlib Require Export Morphisms.
From Stdlib Require Export Setoid.
From Stdlib Require Export Basics. *)

From Stdlib Require Export CMorphisms.
From Stdlib Require Export CEquivalence.
From Stdlib Require Export Datatypes.
From Stdlib Require Utf8.

Global Close Scope program_scope.
Global Set Universe Polymorphism.

Global Set Warnings "-notation-overridden".
Global Set Warnings "-notation-incompatible-format".

(** Keep obligation contexts close to the declared fields, including dependent
    pairs. Mathematical laws are proved explicitly below the data. Declaring
    a class field for a law does not assert a global axiom: constructing a
    model requires supplying that field's proof. General results then take
    the structure and its laws as explicit parameters. *)

(** 义务上下文紧贴声明字段，保留依赖对；数学定律在数据之后显式证明。将定律
    声明为类的字段不等于引入全局公理：构造模型时必须提供相应证明，一般结论
    则以结构及其定律作为显式参数。 *)

Ltac cats_obligation := intros; cbn in *.
Global Obligation Tactic := cats_obligation.



(** * Type Notation

    Logical notation here retains constructive witnesses in [Type]. An
    inhabitant of [∃ x, P x] contains both a value and evidence of [P x];
    its first projection retrieves the value. Likewise, [P ∧ Q] is a pair,
    [P ∨ Q] records a chosen alternative, and [P ↔ Q] provides both maps.
    Negation is a map into [Empty_set].

    This convention lets a universal property return a mediator that later
    definitions can compute with. Extracting a stored witness is projection
    of existing data, so it needs no choice principle. It must be
    distinguished from extracting data from a Prop-only existence proof. *)

(** * Type 值逻辑记号

    此处的逻辑记号在 [Type] 中保留构造见证。[∃ x, P x] 的元素同时包含一个值
    及 [P x] 的证据，第一投影可以取出这个值。同样，[P ∧ Q] 是一对数据，
    [P ∨ Q] 记录所选的分支，[P ↔ Q] 给出双向映射；否定是到 [Empty_set] 的映射。

    这个约定使泛性质能够返回供后续定义计算的中介。取出已保存的见证只是投影
    已有数据，不需要选择原理；这与从仅有 Prop 存在性的证明中提取数据不同。 *)

Module Export TypeLogic.
Export Utf8.

(* Notation "'∀' x .. y , P" := (forall x, .. (forall y, P)..)
  (at level 10, x binder, y binder, P at level 200,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope. *)

Local Disable Notation "∃ x .. y , P".
Notation "∃ x .. y , P" := (sigT (λ x, .. (sigT (λ y, P))..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[ ' '[ ' ∃  x .. y ']' , '/' P ']'") : type_scope.

Notation "x ∨ y" := (sum x y)
  (at level 85, right associativity, only parsing) : type_scope.
Notation "x ∧ y" := (prod x y)
  (at level 80, right associativity, only parsing) : type_scope.

Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity, only parsing): type_scope.
Notation "¬ x" := (x → Empty_set)
  (at level 75, right associativity) : type_scope.

Export SigTNotations.
Export Notations.
End TypeLogic.



(** * Meta: Universal Property *)

(** * 元层泛性质 *)

(** A selected solution [x] of [P], unique under the supplied relation [R].
    The field [this] proves [P x]; [that] sends every other solution [y]
    to a witness of [R y x]. No equality between proofs of [P] is requested.

    Full unique existence is expressed by [∃ x, is_unique P x]. The outer
    dependent pair selects the solution, while [is_unique] states its
    property and uniqueness. For a categorical universal property, [x]
    will typically be an arrow and [R] its specified hom equality. *)

(** [P] 的选定解 [x] 在给定关系 [R] 下唯一。字段 [this] 证明 [P x]，[that]
    为任意另一个解 [y] 给出 [R y x] 的见证，不要求比较 [P] 的证明是否相等。

    完整的唯一存在写作 [∃ x, is_unique P x]：外层依赖对选取解，[is_unique]
    陈述其性质与唯一性。用于范畴泛性质时，[x] 通常是态射，[R] 则为指定的
    Hom 相等。 *)

Record is_unique {X R} `{Equivalence X R}
    (P : X → Type) (x : X)
  : Type
  :=
  { this : P x
  ; that : ∀ y : X, P y → R y x
  }.

(** ** Uniqueness under a Specified Equivalence

    Fix a type [X] and a Type-valued equivalence relation [R]. Relate
    unique-element witnesses to comparison with a chosen element, always using
    [R] for equality. *)

(** ** 指定等价下的唯一性

    固定类型 [X] 及 Type 值等价关系 [R]，联系唯一元素见证与同选定元素的比较，相等始终使用 [R]。 *)

Section Unique.
Context {X : Type} {R : X → X → Type} `{Equivalence X R}.

(** Uniqueness among all elements under [R], using the always-satisfied
    predicate. The result says that every element is equivalent to [x],
    not that their carrier representations are natively equal. *)

(** 以恒成立的谓词表达元素在全体元素中的 [R] 唯一性：每个元素都与 [x] 等价，
    无需其载体表示在原生相等意义下相同。 *)

Definition is_unique_element (x : X)
  : Type
  := is_unique (λ _, True) x.

(** Uniqueness of an element is equivalent to every element being equivalent
    to it. *)

(** 元素唯一等价于每个元素都与它等价。 *)

Theorem unique_element_iff {x : X}
  : is_unique_element x ↔ ∀ y : X, R y x.
Proof. firstorder. Qed.

End Unique.

Tactic Notation "elim_unique" constr(H) "as" ident(Hyp) :=
  let Hsat := fresh Hyp "_sat" in
  let Heq := fresh Hyp "_eq" in
  destruct H as [Hsat Heq].

Tactic Notation "elim_unique_eq" constr(H) "as" ident(Hyp) :=
  let Heq := fresh Hyp "_eq" in
  destruct H as [_ Heq].

Tactic Notation "elim_unique" constr(H) "with" constr(h) :=
  let Heq := fresh "Heq" in
  destruct H as [_ Heq];
  specialize (Heq h).



(** ** Equivalence of Prod Types *)

(** ** 乘积类型的等价 *)

Section ProdEquivalence.
Context {X Y} (Rx : crelation X) (Ry : crelation Y).

(** Compare a pair componentwise, using [Rx] for the first component and
    [Ry] for the second. A witness consists of the two component witnesses.
    This construction later supplies the hom equality of product categories,
    without native equality of pairs or equality of witness fields. *)

(** 逐分量比较有序对，第一分量使用 [Rx]，第二分量使用 [Ry]；关系见证就是
    两个分量见证组成的一对。后面乘积范畴的 Hom 相等复用此构造，不要求有序对
    的原生相等，也不比较见证字段。 *)

Definition ProdEq
  : crelation (X * Y)
  := λ '(x1, y1) '(x2, y2), Rx x1 x2 ∧ Ry y1 y2.

Context `{Equivalence X Rx} `{Equivalence Y Ry}.

(** [ProdEq] is an equivalence relation. *)

(** [ProdEq] 是等价关系。 *)

Global Program Instance ProdEq_Equivalence
  : Equivalence ProdEq.
Next Obligation. intros [x y]. simpl. split; reflexivity. Qed.
Next Obligation. intros [x1 y1] [x2 y2] [H1 H2].
  split; symmetry; auto.
Qed.
Next Obligation.
  intros [x1 y1] [x2 y2] [x3 y3] [Hx1 Hy1] [Hx2 Hy2].
  split; etransitivity; eauto.
Qed.

End ProdEquivalence.
