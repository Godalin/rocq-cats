From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Bicategory.Core.
From Cats Require Import
  Cat.CatCat
  Cat.Bicategory.Homotopy.

(** * Categories, Functors and All Natural Transformations

    The hom-categories are [FctCat], with [NatEq] on their morphisms. Identity
    and composition of functors agree on actions, but their proof-bearing
    records need not be Rocq-equal. We therefore retain the canonical
    associators and unitors and verify bicategory coherence, without claiming
    native strictness. *)

(** * 范畴、函子与全部自然变换

    Hom 范畴取 [FctCat]，其态射按 [NatEq] 相等。函子恒等和复合的作用一致，但含证
    明的记录未必原生相等；因此保留结合子和单位子并验证双范畴相干性，不要求原生
    严格性。 *)

Program Definition CatBicat
  : Bicat
  :=
  {|ObB := Cat
  ; HomCat := FctCat
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

(** Bicategorical left whiskering in Cat agrees with functor whiskering. *)

(** 范畴双范畴的左须化与函子须化一致。 *)

Theorem cat_whisker_l {C D E : Cat} (G : Fct D E)
    {F F' : Fct C D} (α : F ⇒ F')
  : whisker_l (K := CatBicat) G α ≈N (G ∘Nl α).
Proof. intros X. exact (comp_id_l (fmap G (α X))). Qed.

(** Bicategorical right whiskering in Cat agrees with functor whiskering. *)

(** 范畴双范畴的右须化与函子须化一致。 *)

Theorem cat_whisker_r {C D E : Cat} {G G' : Fct D E}
    (β : G ⇒ G') (F : Fct C D)
  : whisker_r (K := CatBicat) β F ≈N (β ∘Nr F).
Proof.
  intros X. change (β (F X) ∘ fmap G (@id (F X)) ≈ β (F X)).
  rewrite functor_id. apply comp_id_r.
Qed.

(** ** Comparison with the Existing Category of Categories *)

(** ** 与既有范畴之范畴的比较 *)

(** Invertible two-cells in the category bicategory are natural isomorphisms. *)

(** 范畴双范畴的可逆二胞就是自然同构。 *)

Definition cat_bicat_homotopy_eq {C D : Cat} (F G : Fct C D)
  : @Cats.Cat.Core.HomEq (BicatHomotopyCat CatBicat) C D F G ↔ F ≅N G.
Proof.
  split; intros H.
  - exact (H.1; is_iso_NatIso H.1 H.2).
  - exact (H.1; NatIso_is_iso H.1 H.2).
Defined.

(** Send the homotopy category of the category bicategory to CatCat. *)

(** 将范畴双范畴的同伦范畴送到 [CatCat]。 *)

Program Definition ToCatCatF
  : Fct (BicatHomotopyCat CatBicat) CatCat
  :=
  {|F0 C := C
  ; F1 C D F := F
  ; functor_fmap_proper C D F G H := fst (cat_bicat_homotopy_eq F G) H
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** View CatCat functors in the homotopy category of the category bicategory. *)

(** 在范畴双范畴的同伦范畴中解释 [CatCat] 的函子。 *)

Program Definition FromCatCatF
  : Fct CatCat (BicatHomotopyCat CatBicat)
  :=
  {|F0 C := C
  ; F1 C D F := F
  ; functor_fmap_proper C D F G H := snd (cat_bicat_homotopy_eq F G) H
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** The homotopy category of the category bicategory is equivalent to CatCat. *)

(** 范畴双范畴的同伦范畴等价于 [CatCat]。 *)

Definition cat_bicat_homotopy_equiv
  : BicatHomotopyCat CatBicat ≃C CatCat.
Proof.
  exists ToCatCatF, FromCatCatF. split.
  - unshelve notypeclasses refine (({|nt := _
                                    |}); _).
    + exact (λ C, @IdF C).
    + intros C D F. apply (snd (cat_bicat_homotopy_eq _ _)).
      transitivity F; [apply CompF_id_l | symmetry; apply CompF_id_r].
    + intros C. exists (@IdF C). split;
        apply (snd (cat_bicat_homotopy_eq _ _)); apply CompF_id_l.
  - unshelve notypeclasses refine (({|nt := _
                                    |}); _).
    + exact (λ C, @IdF C).
    + intros C D F.
      transitivity F; [apply CompF_id_l | symmetry; apply CompF_id_r].
    + intros C. exists (@IdF C). split; apply CompF_id_l.
Defined.
