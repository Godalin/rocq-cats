From Cats Require Import
  Algebra.Group.Cocycle.

Local Open Scope algebra_scope.

(** * Missing Labels at Independent Sizes

    Check both strict carrier/equality size orders. The four completion
    functions below require groups only, without a commutativity instance. *)

Section Sizes.
Universes e h.
Constraint e < h.
Context (M : Group@{h e _}) (N : Group@{e h _}).

(** Low equality retains the selected first factor and its uniqueness. *)

Definition low_first_solution (q r s : M)
  : ∃ p : M, is_unique (R := carrier_equiv M)
      (λ p, p ⋅ q ≈S r ⋅ s) p
  := Cocycle012Solution q r s.

(** High equality also permits a selected second factor. *)

Definition high_second_solution (p r s : N)
  : ∃ q : N, is_unique (R := carrier_equiv N)
      (λ q, p ⋅ q ≈S r ⋅ s) q
  := Cocycle023Solution p r s.

(** The right side keeps the original orientation of the equation. *)

Definition low_third_solution (p q s : M)
  : ∃ r : M, is_unique (R := carrier_equiv M)
      (λ r, p ⋅ q ≈S r ⋅ s) r
  := Cocycle123Solution p q s.

(** The last solution keeps equality witnesses at their higher size. *)

Definition high_last_solution (p q r : N)
  : ∃ s : N, is_unique (R := carrier_equiv N)
      (λ s, p ⋅ q ≈S r ⋅ s) s
  := Cocycle013Solution p q r.

(** Properness can be used to form a low-equality respectful function. *)

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

Section Consistency.
Universes e h.
Constraint e < h.
Context (M : Group@{h e _}) (N : Group@{e h _})
    `{CM : !IsCommMagma M} `{CN : !IsCommMagma N}.

(** The last tetrahedron equation keeps the lower equality universe. *)

Definition low_last_equation (a b c d e f g h i j : M)
    (H0 : g ⋅ i ≈S j ⋅ h) (H1 : d ⋅ f ≈S j ⋅ e)
    (H2 : b ⋅ f ≈S i ⋅ c) (H3 : a ⋅ e ≈S h ⋅ c)
  : a ⋅ d ≈S g ⋅ b
  := cocycle_tetrahedron_0123 a b c d e f g h i j H0 H1 H2 H3.

(** The first tetrahedron equation permits the opposite native profile. *)

Definition high_first_equation (a b c d e f g h i j : N)
    (H1 : d ⋅ f ≈S j ⋅ e) (H2 : b ⋅ f ≈S i ⋅ c)
    (H3 : a ⋅ e ≈S h ⋅ c) (H4 : a ⋅ d ≈S g ⋅ b)
  : g ⋅ i ≈S j ⋅ h
  := cocycle_tetrahedron_1234 a b c d e f g h i j H1 H2 H3 H4.

End Consistency.
