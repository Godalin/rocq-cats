From Cats Require Import Cat.Core Cat.Functor Cat.Natural.

(** * Categories and Functors up to Natural Isomorphism

    Morphism equivalence retains a natural isomorphism as data. Consequently,
    an isomorphism in this category is an equivalence of categories, with chosen
    quasi-inverse functors and natural isomorphisms for the two composites.
    This is a one-dimensional shadow; all natural transformations are retained
    separately by the hom-categories in [CatBicat]. *)

Global Instance CatCat : Cat :=
  {| Ob := Cat
   ; Hom := Functor
   ; HomEq _ _ := NatIso
   ; HomEq_Equivalence _ _ := NatIso_Equivalence
   ; id _ := IdF
   ; comp _ _ _ := CompF
   ; comp_proper _ _ _ := CompF_proper
   ; comp_id_r _ _ := CompF_id_r
   ; comp_id_l _ _ := CompF_id_l
   ; comp_assoc _ _ _ _ := CompF_assoc |}.

Notation "C '≃C' D" := (C ≅[CatCat] D)
  (at level 70, no associativity) : cat_scope.

(** ** Opposite Categories *)

Definition op_involution (C : Cat) : C ^op ^op ≃C C.
Proof.
  exists FromDoubleOpF, ToDoubleOpF. split.
  - unshelve refine ((@mkNat (C ^op ^op) (C ^op ^op)
      (ToDoubleOpF ∘F FromDoubleOpF) IdF (λ X, id) _); _).
    + intros X Y f. simpl. carw.
    + intros X. exists id. split; apply comp_id_l.
  - unshelve refine ((@mkNat C C
      (FromDoubleOpF ∘F ToDoubleOpF) IdF (λ X, id) _); _).
    + intros X Y f. simpl. carw.
    + intros X. exists id. split; apply comp_id_l.
Defined.

Definition OpCatF : Functor CatCat CatCat.
Proof.
  refine (@Build_Functor CatCat CatCat op (λ C D F, OpF F)
    (λ C D, @OpF_proper C D) _ _).
  - intros C. apply OpF_id.
  - intros C D E G F. apply OpF_comp.
Defined.

(** The double-opposite comparison is natural in the category. Its
    naturality compares functors by natural isomorphism. *)
Definition OpInvolutionN : (OpCatF ∘F OpCatF) => (@IdF CatCat).
Proof.
  refine (@mkNat CatCat CatCat (OpCatF ∘F OpCatF) IdF
    (λ C, FromDoubleOpF (C := C)) _).
  intros C D F.
  unshelve refine ((@mkNat (C ^op ^op) D
    (FromDoubleOpF ∘F OpF (OpF F)) (F ∘F FromDoubleOpF) (λ X, id) _); _).
  - intros X Y f. simpl. carw.
  - intros X. exists id. split; apply comp_id_l.
Defined.

Definition op_involution_nat_iso : (OpCatF ∘F OpCatF) ≅N (@IdF CatCat).
Proof.
  exists OpInvolutionN. intros C. exact (op_involution C).2.
Defined.
