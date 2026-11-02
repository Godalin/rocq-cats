From Cats Require Export Meta.

(** * Sets with Specified Equality

    A set is constructively represented by a carrier and a Type-valued
    equivalence relation (a setoid). Rocq's [eq] is one possible choice;
    equality witnesses need not have the same size as carrier elements. *)

(** * 带指定相等的集合

    集合构造性地表示为载体及 Type 值等价关系，即广集。Rocq 原生相等只是一个具
    体选择，相等见证与元素的大小不必一致。 *)

Declare Scope set_scope.
Delimit Scope set_scope with set.
Open Scope set_scope.

(** A carrier with a Type-valued specified equality and its equivalence laws. *)

(** 带 Type 值指定相等及其等价律的载体。 *)

Record SetC
  :=
  { carrier :> Type
  ; carrier_equiv : crelation carrier
  ; carrier_setoid :: Equivalence carrier_equiv
  }.

Notation "[≈S]" := (carrier_equiv _).

Infix "≈S" := (carrier_equiv _)
  (at level 50) : set_scope.

(** Explicit wrappers raise carrier and equality-witness levels separately.
    Both lower maps compute by projection; no resizing is assumed. *)

(** 显式包装独立提升载体与相等见证的层级，两个降低映射都通过投影计算，不假设大
    小重设。 *)

Record LiftT@{u v} (A : Type@{u})
  : Type@{v}
  :=
  { lower : A }.
Arguments lower {_} _.

(** Raise carrier and equality universes independently by explicit wrappers. *)

(** 通过显式包装独立提升载体与相等宇宙。 *)

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
