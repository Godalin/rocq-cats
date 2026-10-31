From Cats Require Import Cat.Core Cat.Terminal Instance.Set.Core.

(** * An Initial Setoid *)

Program Definition EmptyS@{u r} : SetC@{u r} :=
  {| carrier := Empty_set; carrier_equiv := λ _ _, unit |}.
Next Obligation.
  split; red; intros; exact tt.
Defined.

Program Definition SetCat_HasInitial : HasInitial SetCat :=
  {| Term := EmptyS |}.
Next Obligation.
  intros X. assert (h : EmptyS →r X).
  { unshelve notypeclasses refine {| func := _ |}.
    - exact (λ x, match x with end).
    - intros x. destruct x. }
  exists h.
  split. exact I. intros f _ x. destruct x.
Defined.
