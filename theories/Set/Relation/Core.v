From Cats.Set Require Export Core.

(** * Type-Valued Relations and Inclusion

    Inclusion is the existing [subrelation]: a function transforming each
    relation witness into one with the same endpoints. It does not compare
    predicate functions or discard the witnesses into [Prop]. Carrier and
    witness universes are independent. *)

(** * Type 值关系及其包含

    包含使用已有的 [subrelation]，即把每个关系见证转换为相同端点处的见证。
    它不比较谓词函数，也不将见证丢入 [Prop]。载体与见证的宇宙独立。 *)

Declare Scope relation_scope.
Delimit Scope relation_scope with relation.
Infix "⊆R" := subrelation (at level 70) : relation_scope.
Infix "≈R" := relation_equivalence (at level 70) : relation_scope.
Local Open Scope relation_scope.

(** Identity inclusion returns the supplied witness unchanged. *)

(** 恒等包含原样返回所给见证。 *)

Definition relation_incl_id {A : Type} (R : crelation A)
  : R ⊆R R
  := λ x y h, h.

(** Inclusion composition is ordinary composition of witness transformers. *)

(** 包含的复合就是见证转换函数的通常复合。 *)

Definition relation_incl_comp {A : Type} {R S T : crelation A}
    (h : R ⊆R S) (k : S ⊆R T)
  : R ⊆R T
  := λ x y p, k x y (h x y p).

(** A transparent preorder on relations at a common witness bound. Use this
    value explicitly in closure constructions: the standard library also
    registers an opaque proof of the same preorder, which need not compute.
    No new competing global instance is registered here. *)

(** 共同见证界内关系上的透明预序。闭包构造显式使用此值：标准库也注册了同一
    预序的不透明证明，但它不保证计算。此处不注册相互竞争的全局实例。 *)

Program Definition RelationInclusionPreorder (A : Type)
  : PreOrder (@subrelation A)
  :=
  {|PreOrder_Reflexive R := relation_incl_id R
  ; PreOrder_Transitive R S T h k := relation_incl_comp h k
  |}.

(** Two inclusions give the standard pointwise equivalence of relations.
    This supplies two maps at each endpoint pair, not an isomorphism of
    witness types or equality of relation functions. *)

(** 两个包含给出标准的逐点关系等价：在每对端点处提供两个映射，而不是见证
    类型的同构或关系函数相等。 *)

Definition relation_equiv_of_inclusions {A : Type} {R S : crelation A}
    (h : R ⊆R S) (k : S ⊆R R)
  : R ≈R S
  := λ x y, (@h x y, @k x y).

(** The forward component of pointwise equivalence is an inclusion. *)

(** 逐点等价的正向分量给出包含。 *)

Definition relation_equiv_forward {A : Type} {R S : crelation A}
    (h : R ≈R S)
  : R ⊆R S
  := λ x y, fst (h x y).

(** The reverse component preserves the computational witness as well. *)

(** 反向分量同样保留计算见证。 *)

Definition relation_equiv_backward {A : Type} {R S : crelation A}
    (h : R ≈R S)
  : S ⊆R R
  := λ x y, snd (h x y).
