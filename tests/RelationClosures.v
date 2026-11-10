From Cats.Set.Relation Require Import Equivalence.
From Cats.Set Require Import Generated.

(** * Relation Closure Interface Regressions

    These checks separate carrier, edge and path universes, then observe
    data carried through the generic closure laws and the legacy interface.
    They do not require equality between different derivations. *)

(** * 关系闭包接口回归检查

    这些检查分离载体、边与路径的宇宙，再观察通过一般闭包律及旧接口传递的
    数据；不要求不同推导相等。 *)

Local Open Scope relation_scope.
Local Open Scope set_scope.

Section LargerWitnesses.
Universes a r.
Constraint a < r.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** The chosen endomorphisms retain a witness bound strictly above the
    carrier. In particular, their packaging must not identify these levels. *)

(** 选定自映射保留严格高于载体的见证界，特别是封装不能识别这两个层级。 *)

Definition large_witness_path_closure
  : Closure (@subrelation@{a r r} A)
  := ReflexiveTransitiveClosure A.

Definition large_witness_equivalence_closure
  : Closure (@subrelation@{a r r} A)
  := EquivalenceClosure A.

Definition large_witness_equivalence_comparison
  : R^±* ≈R R^≈
  := equivalence_closure_legacy R.

End LargerWitnesses.

Section SmallerEdges.
Universes a r p.
Constraint r < a.
Constraint a < p.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** Symmetry needs no carrier-sized witness, whereas paths may retain
    intermediate elements in a third, larger universe. *)

(** 对称性不需要与载体同样大的见证；路径则可在第三个更大的宇宙内保留中间
    元素。 *)

Definition small_witness_symmetric_closure
  : Closure (@subrelation@{a r r} A)
  := SymmetricClosure A.

Definition small_edges_large_paths
  : A → A → Type@{p}
  := @ReflTransClosure@{a r p} A R.

Definition small_edges_large_path_step {x y : A} (h : R x y)
  : small_edges_large_paths x y
  := rtc_step h.

End SmallerEdges.

Section WitnessComputations.

(** A relation whose witnesses are observable natural numbers. Composition
    adds the numbers, and the empty path contributes zero. *)

(** 关系见证是可观察的自然数；复合将数相加，空路径贡献零。 *)

Definition WeightedRelation (_ _ : bool)
  : Type
  := nat.

Local Program Instance weighted_relation_PreOrder
  : PreOrder WeightedRelation
  :=
  {|PreOrder_Reflexive x := 0
  ; PreOrder_Transitive x y z h k := (h + k)%nat
  |}.

(** Fold oriented paths without discarding either orientation's payload. *)

(** 折叠带方向的路径，不丢弃任一方向携带的数据。 *)

Definition path_weight {x y : bool} (p : WeightedRelation^±* x y)
  : nat
  := rtc_preserves (S := WeightedRelation) (λ x, x)
      (λ x y h, match h with inl n => n | inr n => n end) p.

Definition weighted_path
  : WeightedRelation^±* false true
  := rtc_trans
      (rtc_step (R := WeightedRelation^±) (x := false) (y := true) (inl 2))
      (rtc_step (R := WeightedRelation^±) (x := true) (y := true) (inr 3)).

(** Generic inflation and flattening must compute through the explicitly
    chosen inclusion preorder and the composite closure construction. *)

(** 一般嵌入与压平须通过显式选定的包含预序及复合闭包构造进行计算。 *)

Example equivalence_inflation_computes
  : path_weight
      (closure_inflate (EquivalenceClosure bool) WeightedRelation
        false true 7) = 7.
Proof. reflexivity. Qed.

Example equivalence_flattening_computes
  : path_weight
      (closure_flatten (EquivalenceClosure bool) WeightedRelation
        true false
        (rtc_step (R := WeightedRelation^±*^±)
          (x := true) (y := false) (inr weighted_path))) = 5.
Proof. reflexivity. Qed.

(** Comparing with the existing derivation-tree interface also preserves
    the payload through both transparent witness transformations. *)

(** 与既有推导树接口的比较，也通过两个透明见证转换保留携带的数据。 *)

Example legacy_comparison_computes
  : path_weight
      (snd (equivalence_closure_legacy WeightedRelation false true)
        (fst (equivalence_closure_legacy WeightedRelation false true)
          weighted_path)) = 5.
Proof. reflexivity. Qed.

End WitnessComputations.
