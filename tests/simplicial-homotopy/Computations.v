From Cats Require Import
  Instance.Set.Simplicial.Homotopy.Core
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Instance.Set.Terminal.

Local Open Scope nat_scope.

(** * Computing with Time and Endpoint Restrictions *)

(** * 时间及端点限制的计算 *)

Definition SmallInterval
  : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Δ[1].

Definition SmallPoint
  : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := ConstF (Δ^op) UnitS@{Set Set}.

Definition PointPath
  : (SimplicialIntervalPointN false : SmallPoint ⇒ SmallInterval)
      ∼Δ SimplicialIntervalPointN true
  := SimplicialPointHomotopy.

(** The stored witness retains the whole nonconstant time edge. *)

(** 存储的见证保留整条非常值时间边。 *)

Example interval_path_computes
  : fin_rank (lower (homotopy_map PointPath 1
      (tt, simplex_generic 1)) (fin_next fin_first)) = 1.
Proof. reflexivity. Qed.

(** Its first restriction chooses vertex zero. *)

(** 第一个限制选取顶点零。 *)

Example initial_endpoint_computes
  : fin_rank (lower ((homotopy_map PointPath ∘Nv
      SimplicialEndpointN SmallPoint false) 0 tt) fin_first) = 0.
Proof. reflexivity. Qed.

(** Its second restriction chooses vertex one. *)

(** 第二个限制选取顶点一。 *)

Example final_endpoint_computes
  : fin_rank (lower ((homotopy_map PointPath ∘Nv
      SimplicialEndpointN SmallPoint true) 0 tt) fin_first) = 1.
Proof. reflexivity. Qed.

(** A constant homotopy keeps its source simplex at every time. *)

(** 恒定同伦在每个时间保留其源单形。 *)

Example constant_homotopy_computes
  : let H := SimplicialConstantHomotopy (@idN _ _ SmallInterval) in
    fin_rank (lower (homotopy_map H 1
      (simplex_generic 1, SimplicialIntervalPointN false 1 tt))
      (fin_next fin_first)) = 1.
Proof. reflexivity. Qed.

(** Precomposition retains the stored time coordinate. *)

(** 预复合保留存储的时间坐标。 *)

Example precomposition_computes
  : let H := SimplicialPreHomotopy PointPath (@idN _ _ SmallPoint) in
    fin_rank (lower (homotopy_map H 1 (tt, simplex_generic 1))
      (fin_next fin_first)) = 1.
Proof. reflexivity. Qed.

(** Postcomposition uses the original underlying witness map. *)

(** 后复合使用原有底层见证映射。 *)

Example postcomposition_computes
  : let H := SimplicialPostHomotopy (@idN _ _ SmallInterval) PointPath in
    fin_rank (lower (homotopy_map H 1 (tt, simplex_generic 1))
      (fin_next fin_first)) = 1.
Proof. reflexivity. Qed.

(** Horizontal composition supplies the same time to the second homotopy. *)

(** 水平复合将同一个时间提供给第二个同伦。 *)

Example horizontal_composition_computes
  : let K := SimplicialIntervalHomotopy SmallInterval in
    let H := SimplicialConstantHomotopy (@idN _ _ SmallInterval) in
    fin_rank (lower (homotopy_map (SimplicialCompHomotopy K H) 1
      (SimplicialIntervalPointN false 1 tt, simplex_generic 1))
      (fin_next fin_first)) = 1.
Proof. reflexivity. Qed.

(** A nontrivial homotopy coexists with distinct boundary maps. *)

(** 非平凡同伦与不同边界映射同时存在。 *)

Example homotopic_points_are_not_equal
  : ¬ ((SimplicialIntervalPointN false : SmallPoint ⇒ SmallInterval) ≈N
      SimplicialIntervalPointN true).
Proof. exact simplicial_interval_points_not_equal. Qed.
