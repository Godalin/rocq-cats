From Stdlib Require Import Utf8.

(** * Meta: Universal Property *)

Record is_unique {X : Type} (P : X → Prop) (x : X) : Prop :=
  { this : P x
  ; that : ∀ y : X, P y → y = x
  }.

Definition is_unique' {X : Type} (x : X) : Prop
  := is_unique (λ _, True) x.

Theorem elim_is_unique' {X} {x : X}
  : is_unique' x ↔ ∀ y : X, y = x.
Proof. firstorder. Qed.
