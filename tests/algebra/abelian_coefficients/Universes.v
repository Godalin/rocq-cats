From Cats Require Import
  Algebra.Group.Equation
  Algebra.Monoid.Commutative.

Local Open Scope algebra_scope.

(** * Coefficients with Independent Equality Sizes

    Test both strict orders between carrier and equality sizes, with law
    witnesses in their own inferred auxiliary universes. *)

Section Sizes.
Universes e h.
Constraint e < h.
Context (M : Group@{h e _}) (N : Group@{e h _})
    `{CM : !IsCommMagma M} `{CN : !IsCommMagma N}.

(** Low equality still retains an actual selected solution and uniqueness. *)

Definition low_equality_solution (a b : M)
  : ∃ x : M, is_unique (R := carrier_equiv M) (λ x, a ⋅ x ≈S b) x
  := GroupMulLSolution a b.

(** The other strict size order permits the same computational interface. *)

Definition high_equality_solution (a b : N)
  : ∃ x : N, is_unique (R := carrier_equiv N) (λ x, x ⋅ a ≈S b) x
  := GroupMulRSolution a b.

(** Properness has an auxiliary size bound, without identifying native sizes. *)

Definition low_equality_solution_map (a : M)
  : M →r M
  := mul_r_solve_resp a.

(** Check the opposite size profile for the other respectful solution map. *)

Definition high_equality_solution_map (a : N)
  : N →r N
  := mul_l_solve_resp a.

(** Interchange uses the semigroup inherited from the already chosen group. *)

Definition low_equality_interchange (a b c d : M)
  : (a ⋅ b) ⋅ (c ⋅ d) ≈S (a ⋅ c) ⋅ (b ⋅ d)
  := mul_interchange (M := GroupToSemigroup M) a b c d.

(** Interchange also works with higher equality witnesses. *)

Definition high_equality_interchange (a b c d : N)
  : (a ⋅ b) ⋅ (c ⋅ d) ≈S (a ⋅ c) ⋅ (b ⋅ d)
  := mul_interchange (M := GroupToSemigroup N) a b c d.

(** The inverse-map comparison retains the lower equality level. *)

Definition low_equality_round_trip (a : M)
  : mul_l_solve_resp a ∘r (a ⋅−) ≈f id_resp
  := mul_l_solve_η a.

(** Test the other direction with higher equality witnesses. *)

Definition high_equality_evaluation (a : N)
  : (−⋅ a) ∘r mul_r_solve_resp a ≈f id_resp
  := mul_r_solve_β a.

End Sizes.
