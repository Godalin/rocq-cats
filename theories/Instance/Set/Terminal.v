From Cats Require Import Cat.Core Cat.Terminal Instance.Set.Core.

(** * A Terminal Setoid *)

Definition UnitS@{u r} : SetC@{u r}.
Proof.
  refine {| carrier := unit; carrier_equiv := λ _ _, unit |}.
  split; red; intros; exact tt.
Defined.

Definition SetCat_HasTerminal : HasTerminal SetCat.
Proof.
  refine {| Term := UnitS |}. intros X.
  exists (@Build_FunS_resp X UnitS (λ _, tt) (λ _ _ _, tt)).
  split. exact I. intros f _ x. exact tt.
Defined.
