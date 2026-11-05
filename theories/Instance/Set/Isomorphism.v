From Cats Require Export
  Cat.Isomorphism
  Instance.Set.Core.

(** * Unique Fibers of Setoid Isomorphisms *)

(** * 广集同构的唯一纤维 *)

(** A setoid isomorphism has a unique preimage of every element. The
    preimage is its chosen inverse, and equality is the specified equality. *)

(** 广集同构为每个元素给出唯一原像；原像为选定逆的值，相等为指定广集相等。 *)

Definition iso_fiber_universal {A B : SetC} (i : A ≅[SetCat] B) (b : B)
  : is_unique (R := carrier_equiv A)
      (λ a, i.1 a ≈S b) (i.2.1 b).
Proof.
  refine {|this := _
          ; that := _
          |}.
  - exact (snd i.2.2 b).
  - intros a H. transitivity (i.2.1 (i.1 a)).
    + symmetry. exact (fst i.2.2 a).
    + exact (@func_proper _ _ i.2.1 _ _ H).
Defined.

(** Mapping a unique fiber into any setoid gives a unique image. The
    candidate retains its source representative and fiber witnesses. *)

(** 将唯一纤维映入任意广集得到唯一的像；候选保留源代表及其纤维见证。 *)

Definition iso_fiber_image_universal {A B D : SetC}
    (i : A ≅[SetCat] B) (r : A →r D) (b : B)
  : is_unique (R := carrier_equiv D)
      (λ d, ∃ a : A, (r a ≈S d) ∧ (i.1 a ≈S b)) (r (i.2.1 b)).
Proof.
  destruct (iso_fiber_universal i b) as [Hβ Hunique].
  refine {|this := _
          ; that := _
          |}.
  - exists (i.2.1 b). split; [reflexivity | exact Hβ].
  - intros d [a [Hr Hi]]. transitivity (r a).
    + symmetry. exact Hr.
    + apply func_proper. exact (Hunique a Hi).
Defined.
