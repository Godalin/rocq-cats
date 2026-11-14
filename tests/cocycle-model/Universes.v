From Cats Require Import
  Instance.Set.Simplicial.Cocycle.Low.

(** * Independent Coefficient and Ambient Sizes

    Exchange the native coefficient carrier/equality profile. For each
    profile, ambient equality may be below or above its ambient carrier.
    The carrier bound also includes the stored cocycle-law witnesses. *)

(** * 独立的系数与环境大小

    交换系数载体／相等的原生配置；对两种配置，环境相等都可低于或高于环境
    载体。载体上界也包含 cocycle 所保存的定律见证。 *)

Section Sizes.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.
Context (M : SetC@{h e}) (N : SetC@{e h})
    (HM : Monoid@{l h e} M) (HN : Monoid@{l e h} N).
Local Existing Instance HM.
Local Existing Instance HN.

(** Ambient equality below the carrier, with lower native equality. *)

(** 环境相等低于载体，原生相等也较低。 *)

Definition low_equality_model
  : Functor (Δ^op) SetCat@{u o _ _ _ _ _}
  := Z²(M).

(** Ambient equality above the carrier, keeping that native profile. *)

(** 保留该原生配置，令环境相等高于载体。 *)

Definition high_equality_model
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

(** Exchange the coefficient profile without identifying its levels. *)

(** 交换系数配置，而不识别其层级。 *)

Definition opposite_native_low_model
  : Functor (Δ^op) SetCat@{u o _ _ _ _ _}
  := Z²(N).

(** The exchanged native profile also permits higher ambient equality. *)

(** 交换后的原生配置也允许更高的环境相等。 *)

Definition opposite_native_high_model
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(N).

(** The triangle constructor accepts coefficients in the exchanged profile. *)

(** 三角形构造接受交换后配置中的系数。 *)

Definition independent_triangle_map
  : N →r opposite_native_low_model 2
  := two_cocycle_triangle_resp.

(** Reading a coefficient unwraps its retained data, without resizing. *)

(** 读取系数只拆开保留的数据，不改变其大小。 *)

Definition independent_triangle_value
  : high_equality_model 2 →r M
  := two_cocycle_triangle_value_resp.

(** Both round trips remain available at opposite ambient size profiles. *)

(** 两个往返律仍适用于相反的环境大小配置。 *)

Definition independent_triangle_round_trip (c : opposite_native_high_model 2)
  : two_cocycle_triangle_resp (two_cocycle_triangle_value_resp c) ≈S c
  := two_cocycle_triangle_η c.

(** Uniqueness of edges uses the ambient Type-valued equality. *)

(** 边的唯一性使用环境 Type 值相等。 *)

Definition independent_edge_uniqueness (c d : low_equality_model 1)
  : c ≈S d
  := two_cocycle_one_unique c d.

(** Operator equality is natural isomorphism of finite ordinal functors. *)

(** 算子相等为有限序数函子之间的自然同构。 *)

Definition independent_operator_comparison {m n : nat}
    (θ φ : (@Hom Δ) m n) (H : θ ≈ φ)
  : high_equality_model[θ]Δ ≈f high_equality_model[φ]Δ
  := simplex_restrict_proper θ φ H.

End Sizes.
