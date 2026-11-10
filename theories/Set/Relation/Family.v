From Cats.Set.Relation Require Export Equivalence.
From Cats.Set.Closure Require Import Pointwise.

(** * Indexed Families of Relations

    A relation compares two elements of the same fiber. The index type is
    raw indexing data, with no specified equality or transport. Operations
    between different fibers will specify both endpoints explicitly.

    Index, carrier and edge-witness universes remain independent. The
    pointwise equivalence closure needs its edge bound to contain the
    carrier, but need not contain the index type. *)

(** * 关系的索引族

    关系比较同一纤维中的两个元素。索引类型只是原始索引数据，没有指定的
    相等或运输；不同纤维之间的操作将显式指定两个端点。

    索引、载体与边见证宇宙保持独立。逐点等价闭包的边界须容纳载体，但不必
    容纳索引类型。 *)

Local Open Scope relation_scope.

(** A fiberwise Type-valued relation with a common witness bound. *)

(** 具有共同见证界的逐纤维 Type 值关系。 *)

Definition RelationFamily@{i a r +} {I : Type@{i}} (A : I → Type@{a})
  : Type
  := ∀ i, A i → A i → Type@{r}.

(** Inclusion preserves the index and transforms the supplied witness. *)

(** 包含保留索引，并转换所给见证。 *)

Definition RelationFamilyLe {I : Type} {A : I → Type}
    (R S : RelationFamily A)
  : Type
  := ∀ i, R i ⊆R S i.

Infix "⊆ᵢ" := RelationFamilyLe (at level 70) : relation_scope.

(** Pointwise equivalence records both witness transformations in each
    fiber, without comparing functions or requiring inverse maps. *)

(** 逐点等价在每个纤维中记录两个方向的见证转换，不比较函数或要求映射互逆。 *)

Definition RelationFamilyEq {I : Type} {A : I → Type}
    (R S : RelationFamily A)
  : Type
  := ∀ i, R i ≈R S i.

Infix "≈ᵢ" := RelationFamilyEq (at level 70) : relation_scope.

(** The transparent inclusion preorder composes witness maps fiberwise.
    It is an explicit value, not an automatically enabled chosen model. *)

(** 透明包含预序逐纤维复合见证映射。它是显式值，不是自动启用的选定模型。 *)

Program Definition RelationFamilyPreorder {I : Type} (A : I → Type)
  : PreOrder (@RelationFamilyLe I A)
  :=
  {|PreOrder_Reflexive R i := relation_incl_id (R i)
  ; PreOrder_Transitive R S T h k i := relation_incl_comp (h i) (k i)
  |}.

(** Two family inclusions determine the specified pointwise equivalence. *)

(** 两个族包含确定所指定的逐点等价。 *)

Definition relation_family_equiv_of_inclusions {I : Type} {A : I → Type}
    {R S : RelationFamily A} (h : R ⊆ᵢ S) (k : S ⊆ᵢ R)
  : R ≈ᵢ S
  := λ i, relation_equiv_of_inclusions (h i) (k i).

(** Pointwise comparison is an equivalence, with transparent identity,
    reversal and composition of the component witness transformations. *)

(** 逐点比较是等价关系，其恒等、反转与复合均为透明的分量见证转换。 *)

Global Instance RelationFamilyEq_Equivalence {I : Type} {A : I → Type}
  : Equivalence (@RelationFamilyEq I A).
Proof.
  split.
  - intros R. apply relation_family_equiv_of_inclusions;
      intros i; exact (relation_incl_id (R i)).
  - intros R S h. apply relation_family_equiv_of_inclusions.
    + exact (λ i, relation_equiv_backward (h i)).
    + exact (λ i, relation_equiv_forward (h i)).
  - intros R S T h k. apply relation_family_equiv_of_inclusions.
    + exact (λ i, relation_incl_comp
        (relation_equiv_forward (h i)) (relation_equiv_forward (k i))).
    + exact (λ i, relation_incl_comp
        (relation_equiv_backward (k i)) (relation_equiv_backward (h i))).
Defined.

(** Equivalence closure is the pointwise lift of the existing closure,
    so its laws reuse the general family construction. *)

(** 等价闭包是已有闭包的逐点提升，因此其定律复用一般的族构造。 *)

Definition FamilyEquivalenceClosure@{i a r +}
    {I : Type@{i}} (A : I → Type@{a})
  : Closure (λ R S : RelationFamily@{i a r _} A, R ⊆ᵢ S)
  := PointwiseClosure (λ i, @subrelation (A i))
      (λ i, EquivalenceClosure (A i)).

Notation "R '^≈ᵢ'" := (FamilyEquivalenceClosure _ R)
  (at level 1) : relation_scope.

(** Closedness is exactly a supplied equivalence structure in every fiber.
    No comparison of the structures or their law fields is required. *)

(** 闭性恰好是在每个纤维中给出等价结构，不要求比较结构或其中的定律字段。 *)

Definition family_equivalence_closure_closed@{i a r +}
    {I : Type@{i}} {A : I → Type@{a}} (R : RelationFamily@{i a r _} A)
  : is_closed (FamilyEquivalenceClosure A) R ↔
      ∀ j, Equivalence@{a r} (R j)
  := ((λ h j, fst (@equivalence_closure_closed@{a r _} (A j) (R j)) (h j)),
      (λ h j, snd (@equivalence_closure_closed@{a r _} (A j) (R j)) (h j))).

(** The chosen pointwise closure respects the specified family equivalence. *)

(** 选定逐点闭包保持所指定的族等价。 *)

Global Instance FamilyEquivalenceClosure_proper {I : Type} {A : I → Type}
  : Proper (RelationFamilyEq ==> RelationFamilyEq)
      (FamilyEquivalenceClosure A).
Proof.
  intros R S h. apply relation_family_equiv_of_inclusions.
  - exact (closure_monotone (FamilyEquivalenceClosure A)
      (λ i, relation_equiv_forward (h i))).
  - exact (closure_monotone (FamilyEquivalenceClosure A)
      (λ i, relation_equiv_backward (h i))).
Defined.
