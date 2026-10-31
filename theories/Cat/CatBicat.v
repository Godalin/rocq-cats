From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Bicategory.
From Cats Require Import Cat.CatCat Cat.BicatHomotopy.

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

(** ** Comparison with the Existing Category of Categories *)

Definition cat_bicat_homotopy_eq {C D : Cat} (F G : Functor C D)
  : @Cats.Cat.Core.HomEq (BicatHomotopyCat CatBicat) C D F G ↔ F ≅N G.
Proof.
  split; intros H.
  - exact (H.1; is_iso_NatIso H.1 H.2).
  - exact (H.1; NatIso_is_iso H.1 H.2).
Defined.

Program Definition ToCatCatF : Functor (BicatHomotopyCat CatBicat) CatCat :=
  {| F0 C := C
   ; F1 C D F := F
   ; functor_fmap_proper C D F G H := fst (cat_bicat_homotopy_eq F G) H
   |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

Program Definition FromCatCatF : Functor CatCat (BicatHomotopyCat CatBicat) :=
  {| F0 C := C
   ; F1 C D F := F
   ; functor_fmap_proper C D F G H := snd (cat_bicat_homotopy_eq F G) H
   |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

Definition cat_bicat_homotopy_equiv : BicatHomotopyCat CatBicat ≃C CatCat.
Proof.
  exists ToCatCatF, FromCatCatF. split.
  - unshelve notypeclasses refine (({| nt := _ |}); _).
    + exact (λ C, @IdF C).
    + intros C D F. apply (snd (cat_bicat_homotopy_eq _ _)).
      transitivity F; [apply CompF_id_l | symmetry; apply CompF_id_r].
    + intros C. exists (@IdF C). split;
        apply (snd (cat_bicat_homotopy_eq _ _)); apply CompF_id_l.
  - unshelve notypeclasses refine (({| nt := _ |}); _).
    + exact (λ C, @IdF C).
    + intros C D F.
      transitivity F; [apply CompF_id_l | symmetry; apply CompF_id_r].
    + intros C. exists (@IdF C). split; apply CompF_id_l.
Defined.
