From Cats Require Import
  Instance.Set.Simplicial.Cocycle.Low.

(** * Independent Coefficient and Ambient Sizes

    Exchange the native coefficient carrier/equality profile. For each
    profile, ambient equality may be below or above its ambient carrier.
    The carrier bound also includes the stored cocycle-law witnesses. *)

Section Sizes.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.
Context (M : Monoid@{h e l}) (N : Monoid@{e h l}).

(** Ambient equality below the carrier, with lower native equality. *)

Definition low_equality_model
  : Fct (Δ^op) SetCat@{u o _ _ _ _ _}
  := Z²(M).

(** Ambient equality above the carrier, keeping that native profile. *)

Definition high_equality_model
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

(** Exchange the coefficient profile without identifying its levels. *)

Definition opposite_native_low_model
  : Fct (Δ^op) SetCat@{u o _ _ _ _ _}
  := Z²(N).

(** The exchanged native profile also permits higher ambient equality. *)

Definition opposite_native_high_model
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(N).

(** The triangle constructor accepts coefficients in the exchanged profile. *)

Definition independent_triangle_map
  : N →r opposite_native_low_model 2
  := two_cocycle_triangle_resp.

(** Reading a coefficient unwraps its retained data, without resizing. *)

Definition independent_triangle_value
  : high_equality_model 2 →r M
  := two_cocycle_triangle_value_resp.

(** Both round trips remain available at opposite ambient size profiles. *)

Definition independent_triangle_round_trip (c : opposite_native_high_model 2)
  : two_cocycle_triangle_resp (two_cocycle_triangle_value_resp c) ≈S c
  := two_cocycle_triangle_η c.

(** Uniqueness of edges uses the ambient Type-valued equality. *)

Definition independent_edge_uniqueness (c d : low_equality_model 1)
  : c ≈S d
  := two_cocycle_one_unique c d.

(** Operator equality is natural isomorphism of finite ordinal functors. *)

Definition independent_operator_comparison {m n : nat}
    (θ φ : (@Hom Δ) m n) (H : θ ≈ φ)
  : high_equality_model[θ]Δ ≈f high_equality_model[φ]Δ
  := simplex_restrict_proper θ φ H.

End Sizes.
