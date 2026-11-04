From Cats Require Export
  Graph.Path.

(** * Opposite Graphs and Reversed Paths *)

(** * 反图与反向路径 *)

(** Reverse edge endpoints, retaining the original edge setoids. *)

(** 反转边的端点，保留原边广集。 *)

Program Definition OpGraph (G : Graph)
  : Graph
  :=
  {|Vertex := @Vertex G
  ; EdgeSet x y := @EdgeSet G y x
  |}.

Notation "G '^opG'" := (OpGraph G)
  (at level 20, left associativity) : graph_scope.

(** Reverse a path and its order of concatenation. *)

(** 反转路径及其连接顺序。 *)

Fixpoint path_op {G : Graph} {x y} (p : x →*[G] y)
  : y →*[G^opG] x
  := match p with
  | path_id x => @path_id (G^opG) x
  | path_edge e => @path_edge (G^opG) _ _ e
  | path_comp q p => @path_comp (G^opG) _ _ _ (path_op p) (path_op q)
  end.

(** Read an opposite path back in the original graph. This explicit adapter
    avoids requiring equality of graph records. *)

(** 将反向路径读回原图；显式适配避免要求图记录相等。 *)

Fixpoint path_unop {G : Graph} {x y} (p : x →*[G^opG] y)
  : y →*[G] x
  := match p with
  | path_id x => @path_id G x
  | path_edge e => @path_edge G _ _ e
  | path_comp q p => @path_comp G _ _ _ (path_unop p) (path_unop q)
  end.

Notation "p '^opP'" := (path_op p)
  (at level 35) : graph_scope.
Notation "p '^unopP'" := (path_unop p)
  (at level 35) : graph_scope.

(** Reversal preserves generated path equality, including the reversed
    unit and associativity laws. *)

(** 路径反转保持生成相等，包括反向的单位律和结合律。 *)

Global Instance path_op_proper {G : Graph} {x y}
  : Proper (PathEq ==> PathEq) (@path_op G x y).
Proof.
  intros p q H. induction H; cbn.
  - reflexivity.
  - symmetry. assumption.
  - etransitivity; eassumption.
  - apply path_edge_equiv. assumption.
  - apply path_comp_equiv; assumption.
  - apply path_id_l.
  - apply path_id_r.
  - symmetry. apply path_assoc.
Defined.

(** Reading opposite paths back also preserves their specified equality. *)

(** 将反路径读回也保持其指定相等。 *)

Global Instance path_unop_proper {G : Graph} {x y}
  : Proper (PathEq ==> PathEq) (@path_unop G x y).
Proof.
  intros p q H. induction H; cbn.
  - reflexivity.
  - symmetry. assumption.
  - etransitivity; eassumption.
  - apply path_edge_equiv. assumption.
  - apply path_comp_equiv; assumption.
  - apply path_id_l.
  - apply path_id_r.
  - symmetry. apply path_assoc.
Defined.

(** Reversing and reading back recover the original path by path equality. *)

(** 先反转再读回，按路径相等恢复原路径。 *)

Lemma path_unop_op {G : Graph} {x y} (p : x →*[G] y)
  : path_unop (path_op p) ≈P p.
Proof. induction p; cbn; [reflexivity | reflexivity |].
  apply path_comp_equiv; assumption.
Defined.

(** Reading back and reversing recover an opposite path. *)

(** 先读回再反转，恢复反路径。 *)

Lemma path_op_unop {G : Graph} {x y} (p : x →*[G^opG] y)
  : path_op (path_unop p) ≈P p.
Proof. induction p; cbn; [reflexivity | reflexivity |].
  apply path_comp_equiv; assumption.
Defined.
