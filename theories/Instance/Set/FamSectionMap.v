From Cats Require Import Cat.Core Instance.Set.Core Instance.Set.Fam.
From Cats Require Import Instance.Set.FamCat Instance.Set.FamSection.
From Cats Require Import Instance.Set.FamFibration.

(** * Family Morphisms Acting on Sections *)

Definition section_map {U V : FamC} (φ : FamF U V) (s : SectionS_resp U)
  : SectionS_resp V[famF_base φ]S.
Proof.
  refine (@Build_SectionS_resp (famC_base U) V[famF_base φ]S
    (λ x, famF_fam φ x (s x)) _).
  intros x y p.
  change (transpS V (@func_proper _ _ (famF_base φ) x y p)
    (famF_fam φ x (s x)) ≈S famF_fam φ y (s y)).
  transitivity (famF_fam φ y (transpS U p (s x))).
  - symmetry. apply famF_naturality.
  - apply func_proper. exact (section_proper s p).
Defined.

Infix "▷" := section_map (at level 40, left associativity) : cat_scope.

Global Instance section_map_proper {U V : FamC} (φ : FamF U V)
  : Proper (SectionEq ==> SectionEq) (section_map φ).
Proof. intros s t H x. apply func_proper. exact (H x). Qed.

Definition section_map_resp {U V : FamC} (φ : FamF U V)
  : SectionS U →r SectionS V[famF_base φ]S :=
  @Build_FunS_resp (SectionS U) (SectionS V[famF_base φ]S)
    (section_map φ) (section_map_proper φ).

(** A section over an arbitrary map into the source family can also be
    mapped fiberwise. The output lies over the composite base map. *)
Definition section_map_over {X : SetC} {U V : FamC} (φ : FamF U V)
    (f : X →r famC_base U) (s : SectionS_resp U[f]S)
  : SectionS_resp V[famF_base φ ∘r f]S.
Proof.
  refine (@Build_SectionS_resp X V[famF_base φ ∘r f]S
    (λ x, famF_fam φ (f x) (s x)) _).
  intros x y p.
  change (transpS V (@func_proper _ _ (famF_base φ ∘r f) x y p)
    (famF_fam φ (f x) (s x)) ≈S famF_fam φ (f y) (s y)).
  pose (q := @func_proper _ _ f x y p).
  transitivity (transpS V (@func_proper _ _ (famF_base φ) _ _ q)
    (famF_fam φ (f x) (s x))).
  - apply transpS_witness_independent.
  - transitivity (famF_fam φ (f y) (transpS U q (s x))).
    + symmetry. apply famF_naturality.
    + apply func_proper. exact (section_proper s p).
Defined.

Notation "φ '▷[' f ']' s" := (section_map_over φ f s)
  (at level 40, left associativity, format "φ  ▷[ f ]  s") : cat_scope.

Global Instance section_map_over_proper {X : SetC} {U V : FamC}
    (φ : FamF U V) (f : X →r famC_base U)
  : Proper (SectionEq ==> SectionEq) (section_map_over φ f).
Proof. intros s t H x. apply func_proper. exact (H x). Qed.

(** Equivalent family morphisms may have different base representatives.
    Their images are compared after transport along the retained base witness. *)
Theorem section_map_equiv {U V : FamC} {φ ψ : FamF U V}
    (Hφψ : FamFEq φ ψ) {s t : SectionS_resp U} (Hst : s ≈s t)
  : ∃ p : famF_base φ ≈f famF_base ψ,
      ∀ x, transpS V (p x) ((φ ▷ s) x) ≈S (ψ ▷ t) x.
Proof.
  destruct Hφψ as [p Hp]. exists p. intros x.
  transitivity (famF_fam ψ x (s x)).
  - exact (Hp x (s x)).
  - apply func_proper. exact (Hst x).
Qed.

Theorem section_map_id {U : FamC} (s : SectionS_resp U) (x : famC_base U)
  : (fam_id ▷ s) x ≈S s x.
Proof. reflexivity. Qed.

Theorem section_map_comp {U V W : FamC} (ψ : FamF V W) (φ : FamF U V)
    (s : SectionS_resp U)
  : (fam_comp ψ φ ▷ s) ≈s (ψ ▷[famF_base φ] (φ ▷ s)).
Proof. intros x. reflexivity. Qed.

(** The action over a base map is the ordinary action of the corresponding
    reindexed family morphism, followed by the identity comparison on sections. *)
Theorem section_map_reindex_family {X : SetC} {U V : FamC} (φ : FamF U V)
    (f : X →r famC_base U) (s : SectionS_resp U[f]S)
  : (φ⟦f⟧ ▷ s) ≈s section_reindex (φ ▷[f] s) (id_resp (X := X)).
Proof. intros x. reflexivity. Qed.

(** Reindexing and mapping agree on values in the same fiber. The two
    reindexed family records are related by the composition comparison. *)
Theorem section_map_reindex {X : SetC} {U V : FamC} (φ : FamF U V)
    (s : SectionS_resp U) (f : X →r famC_base U) (x : X)
  : (φ ▷[f] (section_reindex s f)) x ≈S section_reindex (φ ▷ s) f x.
Proof. reflexivity. Qed.

(** Acting on a section commutes with its map into the total space. *)
Theorem section_map_pair {U V : FamC} (φ : FamF U V) (s : SectionS_resp U)
  : (fam_total_resp φ ∘r section_pair_resp U (id_resp (X := famC_base U))
      (section_reindex s (id_resp (X := famC_base U))))
    ≈f section_pair_resp V (famF_base φ) (φ ▷ s).
Proof. intros x. reflexivity. Qed.
