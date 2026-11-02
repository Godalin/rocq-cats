From Cats Require Export Graph.Core.

(** * A Walking Cospan

    Only the two legs are generating edges. Their singleton equalities,
    like the empty edge sets, use Type-valued witnesses. *)
Inductive CospanVertex := cospan_left | cospan_right | cospan_tip.

Definition CospanEdge (x y : CospanVertex) : Type :=
  match x, y with
  | cospan_left, cospan_tip => unit
  | cospan_right, cospan_tip => unit
  | _, _ => Empty_set
  end.

Program Definition CospanGraph : Graph :=
  {| Vertex := CospanVertex
   ; EdgeSet x y := {| carrier := CospanEdge x y; carrier_equiv _ _ := unit |} |}.
Next Obligation. split; repeat intro; exact tt. Defined.

Definition cospan_l : @Edge CospanGraph cospan_left cospan_tip := tt.
Definition cospan_r : @Edge CospanGraph cospan_right cospan_tip := tt.
