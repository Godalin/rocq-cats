From Cats Require Import
  Algebra.Group.Cocycle
  Instance.Set.Simplicial.Cocycle.Kan.

(** * Stable Filling with Only Monoid Coefficients

    Keep coefficient carrier/equality sizes in opposite strict orders,
    and use both strict ambient orders. No group is available here. *)

(** * 仅幺半群系数的稳定填充

    系数载体与相等大小取相反严格次序，环境大小也取两种严格次序。此处不提供
    群结构。 *)

Section MonoidRange.
Universes e h o u p.
Constraint e < h, h < o, o < u, u < p.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Monoid M} `{HN : !Monoid N}.

(** Every stable dimension works with lower ambient equality. *)

(** 每个稳定维度均允许较低环境相等。 *)

Definition monoid_lower_equality_fillers (n : nat)
    (i : Ordinal (S (S (S (S (S n))))))
  : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u o _ _ _ _ _})
      (S (S (S (S (S n))))) i
  := cocycle_higher_HasFillers n i.

(** Higher native and ambient equality also retain actual choices. *)

(** 较高原生及环境相等也保留实际选择。 *)

Definition monoid_higher_equality_fillers (n : nat)
    (i : Ordinal (S (S (S (S (S n))))))
  : HasHornFillers
      (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (S (S (S (S (S n))))) i
  := cocycle_higher_HasFillers n i.

End MonoidRange.

(** ** Three Dimensions Without Commutativity

    Add a group, with no commutativity witness, and test both size orders. *)

(** ** 无交换性假设的三维

    增加群结构，但不提供交换性见证，检查两种大小次序。 *)

Section GroupRange.
Universes e h o u p.
Constraint e < h, h < o, o < u, u < p.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Group M} `{HN : !Group N}.

(** The missing coefficient can have lower native equality. *)

(** 缺失系数允许较低原生相等。 *)

Definition group_lower_equality_fill (i : Ordinal 3)
    (b : HornS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 i)
  : ∃ x, is_horn_filler b x
  := cocycle_horn3_filler i b.

(** The opposite native profile also keeps its full restriction proof. *)

(** 相反原生配置也保留完整限制证明。 *)

Definition group_higher_equality_fill (i : Ordinal 3)
    (b : HornS (Z²(N) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) 3 i)
  : ∃ x, is_horn_filler b x
  := cocycle_horn3_filler i b.

End GroupRange.

(** ** The Complete Kan Interface

    Add commutativity for the critical fourth dimension. Check four
    combinations of coefficient and ambient size orders, then inspect the
    retained witness for arbitrary positive dimensions. *)

(** ** 完整 Kan 接口

    为关键四维增加交换性。检查系数及环境大小次序的四种组合，再读取任意
    正维度保留的见证。 *)

Section KanSizes.
Universes e h o u p.
Constraint e < h, h < o, o < u, u < p.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Group M} `{HN : !Group N}
    `{CM : !IsCommutativeMonoid M} `{CN : !IsCommutativeMonoid N}.

(** Lower coefficient and ambient equality. *)

(** 较低系数相等及环境相等。 *)

Definition lower_native_lower_ambient_Kan
  : HasKanFillers (Z²(M) : Fct (Δ^op) SetCat@{u o _ _ _ _ _})
  := two_cocycle_HasKanFillers.

(** Lower coefficient equality, higher ambient equality. *)

(** 较低系数相等、较高环境相等。 *)

Definition lower_native_higher_ambient_Kan
  : HasKanFillers (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := two_cocycle_HasKanFillers.

(** Higher coefficient equality, lower ambient equality. *)

(** 较高系数相等、较低环境相等。 *)

Definition higher_native_lower_ambient_Kan
  : HasKanFillers (Z²(N) : Fct (Δ^op) SetCat@{u o _ _ _ _ _})
  := two_cocycle_HasKanFillers.

(** Higher coefficient and ambient equality. *)

(** 较高系数相等及环境相等。 *)

Definition higher_native_higher_ambient_Kan
  : HasKanFillers (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := two_cocycle_HasKanFillers.

(** Extract a chosen filler and its equation at an arbitrary dimension. *)

(** 在任意维度提取选定填充及其方程。 *)

Definition lower_ambient_actual_fill (n : nat) (i : Ordinal (S n))
    (b : HornS (Z²(M) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) (S n) i)
  : ∃ x, is_horn_filler b x
  := @horn_fill _ _ _
      (@hasHornFillers _ lower_native_lower_ambient_Kan n i) b.

(** The full matching objects do not force equality to the carrier size. *)

(** 完整匹配对象不会迫使相等大小等于载体大小。 *)

Definition higher_ambient_actual_fill (n : nat) (i : Ordinal (S n))
    (b : HornS (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S n) i)
  : ∃ x, is_horn_filler b x
  := @horn_fill _ _ _
      (@hasHornFillers _ higher_native_higher_ambient_Kan n i) b.

End KanSizes.
