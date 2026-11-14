From Cats Require Import
  Algebra.Group.Cocycle.

Local Open Scope monoid_scope.

(** * Missing Labels at Independent Sizes

    Check both strict carrier/equality size orders. The four completion
    functions below require groups only, without a commutativity instance. *)

(** * 独立大小下的缺失标签

    检查载体与相等大小的两种严格次序。下方四个补全函数只要求群结构，
    不提供交换性实例。 *)

Section Sizes.
Universes e h.
Constraint e < h.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Group M} `{HN : !Group N}.

(** Low equality retains the selected first factor and its uniqueness. *)

(** 较低的相等保留选定的第一因子及唯一性。 *)

Definition low_first_solution (q r s : M)
  : ∃ p : M, is_unique (R := carrier_equiv M)
      (λ p, p ⋅ q ≈S r ⋅ s) p
  := Cocycle012Solution q r s.

(** High equality also permits a selected second factor. *)

(** 较高的相等也允许选定第二因子。 *)

Definition high_second_solution (p r s : N)
  : ∃ q : N, is_unique (R := carrier_equiv N)
      (λ q, p ⋅ q ≈S r ⋅ s) q
  := Cocycle023Solution p r s.

(** The right side keeps the original orientation of the equation. *)

(** 右侧求解保留方程原来的方向。 *)

Definition low_third_solution (p q s : M)
  : ∃ r : M, is_unique (R := carrier_equiv M)
      (λ r, p ⋅ q ≈S r ⋅ s) r
  := Cocycle123Solution p q s.

(** The last solution keeps equality witnesses at their higher size. *)

(** 最后一个解仍将相等见证保留在较高大小。 *)

Definition high_last_solution (p q r : N)
  : ∃ s : N, is_unique (R := carrier_equiv N)
      (λ s, p ⋅ q ≈S r ⋅ s) s
  := Cocycle013Solution p q r.

(** Properness can be used to form a low-equality respectful function. *)

(** 保相等性可用于构造较低相等下的保相等函数。 *)

Program Definition low_solution_map (p q : M)
  : M →r M
  :=
  {|func r := (Cocycle013Solution p q r).1
  |}.
Next Obligation.
  intros r s H. apply cocycle013_solution_proper;
    [reflexivity | reflexivity | exact H].
Defined.

(** The other size order also exposes the unique underlying label. *)

(** 另一种大小次序也可提取唯一的底层标签。 *)

Program Definition high_solution_map (r s : N)
  : N →r N
  :=
  {|func q := (Cocycle012Solution q r s).1
  |}.
Next Obligation.
  intros q q' H. apply cocycle012_solution_proper;
    [exact H | reflexivity | reflexivity].
Defined.

End Sizes.

(** ** Commutative Consistency at Both Sizes

    Add commutativity only for the five-vertex consistency check. *)

(** ** 两种大小下的交换相容性

    仅为五顶点相容性检查增加交换性假设。 *)

Section Consistency.
Universes e h.
Constraint e < h.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Group M} `{HN : !Group N}
    `{CM : !IsCommutativeMonoid M} `{CN : !IsCommutativeMonoid N}.

(** The last tetrahedron equation keeps the lower equality universe. *)

(** 最后一条四面体方程保留较低的相等宇宙。 *)

Definition low_last_equation (a b c d e f g h i j : M)
    (H0 : g ⋅ i ≈S j ⋅ h) (H1 : d ⋅ f ≈S j ⋅ e)
    (H2 : b ⋅ f ≈S i ⋅ c) (H3 : a ⋅ e ≈S h ⋅ c)
  : a ⋅ d ≈S g ⋅ b
  := cocycle_tetrahedron_0123 a b c d e f g h i j H0 H1 H2 H3.

(** The first tetrahedron equation permits the opposite native profile. *)

(** 第一条四面体方程允许相反的原生大小配置。 *)

Definition high_first_equation (a b c d e f g h i j : N)
    (H1 : d ⋅ f ≈S j ⋅ e) (H2 : b ⋅ f ≈S i ⋅ c)
    (H3 : a ⋅ e ≈S h ⋅ c) (H4 : a ⋅ d ≈S g ⋅ b)
  : g ⋅ i ≈S j ⋅ h
  := cocycle_tetrahedron_1234 a b c d e f g h i j H1 H2 H3 H4.

End Consistency.
