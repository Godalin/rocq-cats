From Cats Require Import Cat.Core Cat.Product Instance.Set.Core.

(** * Products in the Category of Setoids *)

Program Canonical ProdS (X Y : SetC) :=
  {|carrier := X * Y
  ; carrier_equiv := ProdEq [≈S] [≈S]
  |}.

Infix "×S" := ProdS (at level 40).

(** Chosen products with computational mediators, extracted from their
    universal property. Equality is pointwise setoid equivalence. *)
Program Definition SetCat_HasProduct : HasProduct SetCat :=
  {| Prod := ProdS
   ; π1 X Y := {| func := fst |}
   ; π2 X Y := {| func := snd |}
   |}.
Next Obligation. intros [x y] [x' y'] [H1 H2]. exact H1. Defined.
Next Obligation. intros [x y] [x' y'] [H1 H2]. exact H2. Defined.
Next Obligation.
  intros Z f g.
  unshelve notypeclasses refine (({| func := _ |}); _).
  - exact (λ z, (f z, g z)).
  - intros z z' Hz. split; apply func_proper; exact Hz.
  - split.
    + split; intros z; reflexivity.
    + intros k [H1 H2] z.
      specialize (H1 z). specialize (H2 z).
      change (fst (k z) ≈S f z) in H1.
      change (snd (k z) ≈S g z) in H2.
      destruct (k z) as [x y]. split; assumption.
Defined.
