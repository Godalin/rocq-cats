From Cats Require Import
  Cat.Core
  Cat.Terminal
  Instance.Set.Core.

(** * An Initial Setoid *)

(** * 始广集 *)

(** The empty carrier as a setoid. *)

(** 空载体所组成的广集。 *)

Program Definition EmptyS@{u r}
  : SetC@{u r}
  :=
  {|carrier := Empty_set
  ; carrier_equiv := λ _ _, unit
  |}.
Next Obligation.
  split; red; intros; exact tt.
Defined.

(** Choose the empty setoid as the initial object. *)

(** 选择空广集作为始对象。 *)

Program Definition SetCat_HasInitial
  : HasInitial SetCat
  :=
  {|hasOpTerminal :=
      {|Term := EmptyS
      |}
  |}.
Next Obligation.
  intros X. assert (h : EmptyS →r X).
  { unshelve notypeclasses refine {|func := _
                                  |}.
    - exact (λ x, match x with end).
    - intros x. destruct x. }
  exists h.
  split. exact I. intros f _ x. destruct x.
Defined.
