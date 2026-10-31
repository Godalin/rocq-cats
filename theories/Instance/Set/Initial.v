From Cats Require Import Cat.Core Instance.Set.Core.

(** * An Initial Setoid *)

Definition EmptyS@{u r} : SetC@{u r}.
Proof.
  refine {| carrier := Empty_set; carrier_equiv := λ _ _, unit |}.
  split; red; intros; exact tt.
Defined.

Definition SetCat_HasInitial : HasInitial SetCat.
Proof.
  refine (@Build_HasTerminal (op SetCat) EmptyS _). intros X.
  exists (@Build_FunS_resp EmptyS X
    (λ x, match x with end) (λ x y _, match x with end)).
  split. exact I. intros f _ x. destruct x.
Defined.
