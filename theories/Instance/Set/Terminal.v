From Cats Require Import
  Cat.Core
  Cat.Terminal
  Instance.Set.Core.

(** * A Terminal Setoid *)

(** * 终广集 *)

(** The singleton setoid. *)

(** 单元素广集。 *)

Program Definition UnitS@{u r}
  : SetC@{u r}
  :=
  {|carrier := unit
  ; carrier_equiv := λ _ _, unit
  |}.
Next Obligation.
  split; red; intros; exact tt.
Defined.

(** Choose the singleton setoid as terminal object. *)

(** 选择单元素广集作为终对象。 *)

Program Definition SetCat_HasTerminal
  : HasTerminal SetCat
  :=
  {|Term := UnitS
  |}.
Next Obligation.
  intros X. assert (h : X →r UnitS).
  { unshelve notypeclasses refine {|func := _
                                  |}.
    - exact (λ _, tt).
    - intros x y p. exact tt. }
  exists h.
  split. exact I. intros f _ x. exact tt.
Defined.
