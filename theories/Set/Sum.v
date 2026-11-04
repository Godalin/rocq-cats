From Cats.Set Require Export
  Morphism.

(** * Binary Disjoint Sums *)

(** * 二元不交和 *)

(** Compare elements within the same summand by its specified equality;
    distinct summands have no equality witnesses. *)

(** 同一加数中的元素按其指定相等比较；不同加数之间没有相等见证。 *)

Definition SumEq {X Y : SetC} (a b : X + Y)
  : Type
  := match a, b with
  | inl x, inl y => x ≈S y
  | inr x, inr y => x ≈S y
  | _, _ => Empty_set
  end.

(** Component equivalence laws give disjoint-sum equivalence. *)

(** 分量等价律给出不交和等价。 *)

Global Instance SumEq_Equivalence {X Y : SetC}
  : Equivalence (@SumEq X Y).
Proof.
  split.
  - intros [x | y]; cbn; reflexivity.
  - intros [x | x] [y | y]; cbn; intros H;
      try destruct H; symmetry; assumption.
  - intros [x | x] [y | y] [z | z]; cbn; intros H K;
      try destruct H; try destruct K; etransitivity; eassumption.
Defined.

(** The foundational disjoint sum keeps carrier and equality universes
    independent. *)

(** 基础不交和保持载体与相等宇宙独立。 *)

Program Canonical SumS (X Y : SetC)
  : SetC
  :=
  {|carrier := X + Y
  ; carrier_equiv := SumEq
  |}.

Infix "+S" := SumS (at level 50, left associativity) : set_scope.

(** Inject into the first summand. *)

(** 注入第一个加数。 *)

Program Definition inl_resp {X Y : SetC}
  : X →r X +S Y
  :=
  {|func := inl
  |}.
Next Obligation. intros x y H. exact H. Defined.

(** Inject into the second summand. *)

(** 注入第二个加数。 *)

Program Definition inr_resp {X Y : SetC}
  : Y →r X +S Y
  :=
  {|func := inr
  |}.
Next Obligation. intros x y H. exact H. Defined.

(** Eliminate a disjoint sum by a respectful map on each summand. *)

(** 用每个加数上的保相等映射消去不交和。 *)

Program Definition sum_case_resp {X Y Z : SetC}
    (f : X →r Z) (g : Y →r Z)
  : X +S Y →r Z
  :=
  {|func a := match a with inl x => f x | inr y => g y end
  |}.
Next Obligation.
  intros [x | x] [y | y] H; cbn in H |- *;
    try destruct H; apply func_proper; assumption.
Defined.
