From Cats Require Export Graph.Core.

(** * A Walking Cospan

    Only the two legs are generating edges. Their singleton equalities, like
    the empty edge sets, use Type-valued witnesses. *)

(** * 步行余跨度

    仅两条腿是生成边；单元素相等与空边集一样使用 Type 值见证。 *)

Inductive CospanVertex
  := cospan_left | cospan_right | cospan_tip.

(** Generators from each outer cospan vertex into its common target. *)

(** 从余跨度各外侧顶点指向共同目标的生成边。 *)

Definition CospanEdge (x y : CospanVertex)
  : Type
  := match x, y with
  | cospan_left, cospan_tip => unit
  | cospan_right, cospan_tip => unit
  | _, _ => Empty_set
  end.

(** The graph with two arrows into one common target. *)

(** 两条箭头指向一个共同目标的图。 *)

Program Definition CospanGraph
  : Graph
  :=
  {|Vertex := CospanVertex
  ; EdgeSet x y :=
      {|carrier := CospanEdge x y
      ; carrier_equiv _ _ := unit
      |}
  |}.
Next Obligation. split; repeat intro; exact tt. Defined.

(** The left generating edge of the cospan graph. *)

(** 余跨度图的左生成边。 *)

Definition cospan_l
  : @Edge CospanGraph cospan_left cospan_tip
  := tt.
(** The right generating edge of the cospan graph. *)

(** 余跨度图的右生成边。 *)

Definition cospan_r
  : @Edge CospanGraph cospan_right cospan_tip
  := tt.

(** * Two Vertices with a Set of Parallel Generators

    The edge set keeps its specified equality; in particular, two distinct
    labels are not identified just because their endpoints agree. *)

(** * 带广集标签的两顶点平行生成边

    边集保留指定相等，不因端点相同就把不同标签等同。 *)

Program Definition LabelledArrowGraph (S : SetC)
  : Graph
  :=
  {|Vertex := bool
  ; EdgeSet x y :=
      if x then {|carrier := Empty_set
                ; carrier_equiv _ _ := unit
                |}
      else if y then S
      else {|carrier := Empty_set
           ; carrier_equiv _ _ := unit
           |}
  |}.
Next Obligation. split; repeat intro; exact tt. Defined.
Next Obligation. split; repeat intro; exact tt. Defined.

(** The two-vertex graph with two independent parallel generators. *)

(** 具有两条独立平行生成边的两顶点图。 *)

Definition ParallelGraph
  : Graph
  := LabelledArrowGraph
    {|carrier := bool
    ; carrier_equiv := eq
    ; carrier_setoid := eq_equivalence
    |}.

(** The first parallel generator. *)

(** 第一条平行生成边。 *)

Definition parallel_l
  : @Edge ParallelGraph false true
  := false.
(** The second parallel generator. *)

(** 第二条平行生成边。 *)

Definition parallel_r
  : @Edge ParallelGraph false true
  := true.
