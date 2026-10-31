From Cats Require Import Cat.Core Cat.Terminal Instance.Set.Core.

(** * A Terminal Setoid *)

Program Definition UnitS@{u r} : SetC@{u r} :=
  {| carrier := unit; carrier_equiv := λ _ _, unit |}.
Next Obligation.
  split; red; intros; exact tt.
Defined.

Program Definition SetCat_HasTerminal : HasTerminal SetCat :=
  {| Term := UnitS |}.
Next Obligation.
  intros X. assert (h : X →r UnitS).
  { unshelve notypeclasses refine {| func := _ |}.
    - exact (λ _, tt).
    - intros x y p. exact tt. }
  exists h.
  split. exact I. intros f _ x. exact tt.
Defined.
