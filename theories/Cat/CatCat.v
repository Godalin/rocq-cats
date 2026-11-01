From Cats Require Import Cat.Core Cat.Functor Cat.Natural.

(** * Categories and Functors up to Natural Isomorphism

    Morphism equivalence retains a natural isomorphism as data. Consequently,
    an isomorphism in this category is an equivalence of categories, with chosen
    quasi-inverse functors and natural isomorphisms for the two composites.
    This is a one-dimensional shadow; all natural transformations are retained
    separately by the hom-categories in [CatBicat]. *)

Global Instance CatCat : Cat :=
  {| Ob := Cat
   ; HomSet C D :=
       {| carrier := Functor C D
        ; carrier_equiv := NatIso
        ; carrier_setoid := NatIso_Equivalence |}
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
  - unshelve notypeclasses refine (({| nt := _ |}); _).
    + exact (λ X, id).
    + intros X Y f. simpl. carw.
    + intros X. exists id. split; apply comp_id_l.
  - unshelve notypeclasses refine (({| nt := _ |}); _).
    + exact (λ X, id).
    + intros X Y f. simpl. carw.
    + intros X. exists id. split; apply comp_id_l.
Defined.

Program Definition OpCatF : Functor CatCat CatCat :=
  {| F0 := op
   ; F1 C D F := OpF F
   ; functor_fmap_proper C D := @OpF_proper C D
   |}.
Next Obligation. apply OpF_id. Defined.
Next Obligation. apply OpF_comp. Defined.

(** The double-opposite comparison is natural in the category. Its
    naturality compares functors by natural isomorphism. *)
Program Definition OpInvolutionN : (OpCatF ∘F OpCatF) => (@IdF CatCat) :=
  {| nt C := FromDoubleOpF (C := C) |}.
Next Obligation.
  unshelve notypeclasses refine (({| nt := _ |}); _).
  - exact (λ X, id).
  - intros A B g. simpl. carw.
  - intros A. exists id. split; apply comp_id_l.
Defined.

Definition op_involution_nat_iso : (OpCatF ∘F OpCatF) ≅N (@IdF CatCat).
Proof.
  exists OpInvolutionN. intros C. exact (op_involution C).2.
Defined.
