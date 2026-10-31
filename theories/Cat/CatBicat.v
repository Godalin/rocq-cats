From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Bicategory.

(** * Categories, Functors and All Natural Transformations

    The hom-categories are [Fct], with [NatEq] on their morphisms. Identity and
    composition of functors agree on actions, but their proof-bearing records
    need not be Rocq-equal. We therefore retain the canonical associators and
    unitors and verify bicategory coherence, without claiming native strictness. *)

Definition CatBicat : Bicat.
Proof.
  refine (@Build_Bicat Cat Fct (λ C, @IdF C) CompNF
    (λ W X Y Z H G F, (@CompF_assoc W X Y Z H G F).1) _
    (λ X Y F, (@CompF_id_l X Y F).1) _
    (λ X Y F, (@CompF_id_r X Y F).1) _ _ _ _ _ _).
  - intros W X Y Z H G F.
    exact (NatIso_is_iso (CompF_assoc H G F).1 (CompF_assoc H G F).2).
  - intros X Y F. exact (NatIso_is_iso (CompF_id_l F).1 (CompF_id_l F).2).
  - intros X Y F. exact (NatIso_is_iso (CompF_id_r F).1 (CompF_id_r F).2).
  - intros A B C D H H' G G' F F' γ β α X. cbn.
    rewrite comp_id_l, comp_id_r, functor_comp, comp_assoc. reflexivity.
  - intros A B F G α X. cbn. carw.
  - intros A B F G α X. cbn. rewrite functor_id. carw.
  - intros A B C D E K H G F X. cbn. repeat rewrite functor_id. carw.
  - intros A B C G F X. cbn. repeat rewrite functor_id. carw.
Defined.

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
