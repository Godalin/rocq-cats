From Cats Require Import
  Instance.Set.Simplicial.TriangleHorn.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Horn Membership at Independent Value Sizes *)

(** ** Lower Equality

    Turn the raw intersection factor into an actual horn element at
    strict carrier/equality sizes, and read one back. Arbitrary operators
    and region witnesses are opaque context; no Kan structure is given. *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2) (s : Ordinal 8) (n : nat).
Let Q
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := SimplicialParameterF (Δ[2] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 2.
Let R
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := Λ[S (simplex_triangle_horn_face_dim s); simplex_triangle_horn_missing r s].

Program Definition lower_old_horn
    (h : (@Hom Δ) n (S (simplex_triangle_horn_face_dim s)))
    (H : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ h)
      (SimplexTriangleHornTimeF r s ∘ h))
  : R n
  :=
  {|lower := (h; triangle_horn_stage_reflect r s h H)
  |}.

Definition lower_horn_old (h : R n)
  : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ (lower h).1)
      (SimplexTriangleHornTimeF r s ∘ (lower h).1)
  := triangle_horn_stage_from_horn r s (lower h).1 (lower h).2.

Definition lower_final_stage (x : Q n)
  : is_triangle_horn_stage r 9 (lower (fst x)) (lower (snd x))
  := triangle_horn_stage_complete r (lower (fst x)) (lower (snd x)).

Definition lower_specified_transport (k : nat) (x y : Q n) (E : x ≈S y)
    (H : is_triangle_horn_stage r k (lower (fst x)) (lower (snd x)))
  : is_triangle_horn_stage r k (lower (fst y)) (lower (snd y)).
Proof.
  destruct x as [[a] [b]], y as [[a'] [b']], E as [[E] [F]].
  exact (triangle_horn_stage_transport r k a a' b b' E F H).
Defined.

End lowerSizes.

(** ** Higher Equality

    Turn the raw intersection factor into an actual horn element at
    strict carrier/equality sizes, and read one back. Arbitrary operators
    and region witnesses are opaque context; no Kan structure is given. *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2) (s : Ordinal 8) (n : nat).
Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialParameterF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2.
Let R
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Λ[S (simplex_triangle_horn_face_dim s); simplex_triangle_horn_missing r s].

Program Definition higher_old_horn
    (h : (@Hom Δ) n (S (simplex_triangle_horn_face_dim s)))
    (H : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ h)
      (SimplexTriangleHornTimeF r s ∘ h))
  : R n
  :=
  {|lower := (h; triangle_horn_stage_reflect r s h H)
  |}.

Definition higher_horn_old (h : R n)
  : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ (lower h).1)
      (SimplexTriangleHornTimeF r s ∘ (lower h).1)
  := triangle_horn_stage_from_horn r s (lower h).1 (lower h).2.

Definition higher_final_stage (x : Q n)
  : is_triangle_horn_stage r 9 (lower (fst x)) (lower (snd x))
  := triangle_horn_stage_complete r (lower (fst x)) (lower (snd x)).

Definition higher_specified_transport (k : nat) (x y : Q n) (E : x ≈S y)
    (H : is_triangle_horn_stage r k (lower (fst x)) (lower (snd x)))
  : is_triangle_horn_stage r k (lower (fst y)) (lower (snd y)).
Proof.
  destruct x as [[a] [b]], y as [[a'] [b']], E as [[E] [F]].
  exact (triangle_horn_stage_transport r k a a' b b' E F H).
Defined.

End higherSizes.
