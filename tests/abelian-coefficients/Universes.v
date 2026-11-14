From Cats Require Import
  Algebra.Group.Equation
  Algebra.Monoid.Commutative.

Local Open Scope monoid_scope.

(** * Coefficients with Independent Equality Sizes

    Test both strict orders between carrier and equality sizes, with law
    witnesses in their own inferred auxiliary universes. *)

(** * 相等大小独立的系数

    测试载体和相等大小的两种严格次序，定律见证位于各自推断的辅助宇宙。 *)

Section Sizes.
Universes e h.
Constraint e < h.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Group M} `{HN : !Group N}
    `{CM : !IsCommutativeMonoid M} `{CN : !IsCommutativeMonoid N}.

(** Low equality still retains an actual selected solution and uniqueness. *)

(** 较低的相等仍保留实际选定的解及唯一性。 *)

Definition low_equality_solution (a b : M)
  : ∃ x : M, is_unique (R := carrier_equiv M) (λ x, a ⋅ x ≈S b) x
  := GroupMulLSolution a b.

(** The other strict size order permits the same computational interface. *)

(** 另一种严格大小次序允许同样的计算接口。 *)

Definition high_equality_solution (a b : N)
  : ∃ x : N, is_unique (R := carrier_equiv N) (λ x, x ⋅ a ≈S b) x
  := GroupMulRSolution a b.

(** Properness has an auxiliary size bound, without identifying native sizes. *)

(** 保相等性使用辅助大小上界，不识别原生大小。 *)

Definition low_equality_solution_map (a : M)
  : M →r M
  := group_mul_r_solve_resp a.

(** Check the opposite size profile for the other respectful solution map. *)

(** 对另一保相等求解映射检查相反的大小配置。 *)

Definition high_equality_solution_map (a : N)
  : N →r N
  := group_mul_l_solve_resp a.

(** Commutativity uses the monoid inherited from the already chosen group. *)

(** 交换性使用从已有选定群继承的幺半群。 *)

Definition low_equality_interchange (a b c d : M)
  : (a ⋅ b) ⋅ (c ⋅ d) ≈S (a ⋅ c) ⋅ (b ⋅ d)
  := monoid_mul_interchange a b c d.

(** Interchange also works with higher equality witnesses. *)

(** 中间因子交换也允许更高的相等见证。 *)

Definition high_equality_interchange (a b c d : N)
  : (a ⋅ b) ⋅ (c ⋅ d) ≈S (a ⋅ c) ⋅ (b ⋅ d)
  := monoid_mul_interchange a b c d.

(** The inverse-map comparison retains the lower equality level. *)

(** 逆映射的比较保留较低相等层级。 *)

Definition low_equality_round_trip (a : M)
  : group_mul_l_solve_resp a ∘r magma_mul_l_resp a ≈f id_resp
  := group_mul_l_solve_η a.

(** Test the other direction with higher equality witnesses. *)

(** 用较高的相等见证测试另一个方向。 *)

Definition high_equality_evaluation (a : N)
  : magma_mul_r_resp a ∘r group_mul_r_solve_resp a ≈f id_resp
  := group_mul_r_solve_β a.

End Sizes.
