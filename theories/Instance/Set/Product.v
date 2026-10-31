From Cats Require Import Cat.Core Instance.Set.Core.

(** * Products in the Category of Setoids *)

Program Canonical ProdS (X Y : SetC) :=
  {|carrier := X * Y
  ; carrier_equiv := ProdEq [≈S] [≈S]
  |}.

Infix "×S" := ProdS (at level 40).

(** Chosen products with computational mediators, extracted from their
    universal property. Equality is pointwise setoid equivalence. *)
Definition SetCat_HasProduct : HasProduct SetCat.
Proof.
  unshelve refine
    {| Prod := ProdS
     ; π1 := λ X Y, @Build_FunS_resp (ProdS X Y) X fst _
     ; π2 := λ X Y, @Build_FunS_resp (ProdS X Y) Y snd _ |}.
  - intros [x y] [x' y'] [H1 H2]. exact H1.
  - intros [x y] [x' y'] [H1 H2]. exact H2.
  - intros X Y Z f g.
    unshelve refine ((@Build_FunS_resp Z (ProdS X Y)
      (λ z, (f z, g z)) _); _).
    + intros z z' Hz. split; apply func_proper; exact Hz.
    + split.
      * split; intros z; reflexivity.
      * intros k [H1 H2] z.
        specialize (H1 z). specialize (H2 z).
        change (fst (k z) ≈S f z) in H1.
        change (snd (k z) ≈S g z) in H2.
        destruct (k z) as [x y]. split; assumption.
Defined.
