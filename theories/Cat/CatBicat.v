From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Bicategory.

(** * Categories, Functors and All Natural Transformations

    The hom-categories are [Fct], with [NatEq] on their morphisms. Identity and
    composition of functors agree on actions, but their proof-bearing records
    need not be Rocq-equal. We therefore retain the canonical associators and
    unitors and verify bicategory coherence, without claiming native strictness. *)

Program Definition CatBicat : Bicat :=
  {| ObB := Cat
   ; HomCat := Fct
   ; id1 C := @IdF C
   ; comp1F := CompNF
   ; associator W X Y Z H G F := (@CompF_assoc W X Y Z H G F).1
   ; left_unitor X Y F := (@CompF_id_l X Y F).1
   ; right_unitor X Y F := (@CompF_id_r X Y F).1
   |}.
Next Obligation.
  apply NatIso_is_iso. exact (CompF_assoc _ _ _).2.
Defined.
Next Obligation. apply NatIso_is_iso. exact (CompF_id_l _).2. Defined.
Next Obligation. apply NatIso_is_iso. exact (CompF_id_r _).2. Defined.
Next Obligation.
  intros A. cbn. rewrite comp_id_l, comp_id_r, functor_comp, comp_assoc. reflexivity.
Defined.
Next Obligation. intros A. cbn. carw. Defined.
Next Obligation. intros A. cbn. rewrite functor_id. carw. Defined.
Next Obligation. intros A. cbn. repeat rewrite functor_id. carw. Defined.
Next Obligation. intros A. cbn. repeat rewrite functor_id. carw. Defined.

Theorem cat_whisker_l {C D E : Cat} (G : Functor D E)
    {F F' : Functor C D} (α : F => F')
  : whisker_l (K := CatBicat) G α ≈N (G ∘Nl α).
Proof. intros X. exact (comp_id_l (fmap G (α X))). Qed.

Theorem cat_whisker_r {C D E : Cat} {G G' : Functor D E}
    (β : G => G') (F : Functor C D)
  : whisker_r (K := CatBicat) β F ≈N (β ∘Nr F).
Proof.
  intros X. change (β (F X) ∘ fmap G (@id (F X)) ≈ β (F X)).
  rewrite functor_id. apply comp_id_r.
Qed.
