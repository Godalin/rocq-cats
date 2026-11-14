From Cats Require Import
  Cat.Core
  Cat.Terminal.



(** Natural-Numbers Object *)

(** 自然数对象。 *)

Definition is_natural_numbers_object {C : Cat} `{HT : !HasTerminal C}
    (N : Ob) (z : Hom 1 N) (s : Hom N N)
  := ∀ X (z' : Hom 1 X) (s' : Hom X X),
    ∃ r : Hom N X,
      is_unique (λ r, r ∘ z ≈ z' ∧ r ∘ s ≈ s' ∘ r) r.

(** Choose a natural-numbers object, zero, successor and its recursion
    property. *)

(** 选择自然数对象、零、后继及其递归性质。 *)

Class HasNaturalNumbersObj (C : Cat) (HT : HasTerminal C)
  :=
  { NNO : Ob
  ; zero : Hom 1 NNO
  ; succ : Hom NNO NNO
  ; nno_universal : is_natural_numbers_object NNO zero succ
  }.

Arguments nno_universal {_ _ _} _ _ _.

(** The recursion mediator from the chosen natural-numbers object. *)

(** 从选定自然数对象出发的递归中介。 *)

Definition rec {C : Cat} `{HT : !HasTerminal C}
    `{HNNO : !HasNaturalNumbersObj C HT} {X}
    (z : Hom 1 X) (s : Hom X X)
  : Hom NNO X
  := (nno_universal X z s).1.

(** The recursor is uniquely determined by its zero and successor equations. *)

(** 递归子由零与后继方程唯一确定。 *)

Theorem nno_rec_unique {C : Cat} `{HT : !HasTerminal C}
    `{HNNO : !HasNaturalNumbersObj C HT} {X} (z : Hom 1 X) (s : Hom X X)
  : is_unique (λ f, f ∘ zero ≈ z ∧ f ∘ succ ≈ s ∘ f) (rec z s).
Proof. exact (nno_universal X z s).2. Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance nno_rec_proper {C : Cat} `{HT : !HasTerminal C}
    `{HNNO : !HasNaturalNumbersObj C HT} {X}
  : Proper (@HomEq[1, X] ==> @HomEq[X, X] ==> @HomEq[NNO, X]) rec.
Proof.
  intros z z' Hz s s' Hs.
  destruct (nno_rec_unique z s) as [[H0 Hsucc] _].
  apply (nno_rec_unique z' s'). split.
  - transitivity z; assumption.
  - transitivity (s ∘ rec z s). exact Hsucc. apply comp_r. exact Hs.
Qed.
