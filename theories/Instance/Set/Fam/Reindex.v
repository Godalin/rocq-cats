From Cats Require Import Cat.Core Cat.Pullback.
From Cats Require Import Instance.Set.Core Instance.Set.Fam.Core Instance.Set.Fam.Cat.

(** * Reindexing Coherent Families *)

Definition ReindexFamC {X : SetC} (U : FamC) (f : X →r famC_base U) : FamC :=
  {| famC_base := X; famC_fam := U[f]S |}.

Notation "U '[' f ']'" := (ReindexFamC U f)
  (at level 8, left associativity, format "U [ f ]") : cat_scope.

(** The canonical family morphism lies over [f] and is the identity on fibers. *)
Program Definition fam_reindex {X : SetC} (U : FamC) (f : X →r famC_base U)
  : FamF U[f] U :=
  {| famF_base := f; famF_fam x := id_resp (X := U (f x)) |}.
Next Obligation. reflexivity. Defined.

(** ** Identity and Composition Comparisons

    The fiber types compute as expected, but the family records also contain
    transport witnesses and coherence proofs. Comparisons use explicit family
    isomorphisms; no equality of those witnesses or proofs is required. *)

Definition fam_reindex_id_iso (U : FamC)
  : U[id_resp (X := famC_base U)] ≅[FamCat] U.
Proof.
  exists (fam_reindex U (id_resp (X := famC_base U))).
  unshelve notypeclasses refine (({| famF_base := _; famF_fam := _ |}); _).
  - exact (id_resp (X := famC_base U)).
  - exact (λ x, id_resp (X := U x)).
  - intros x y p a. simpl. apply transpS_witness_independent.
  - split; exists (λ x, reflS (x := x)); intros x a; apply transpS_id.
Defined.

(** Iterated reindexing compares to reindexing along the composite. *)
Program Definition fam_reindex_comp {X Y : SetC} (U : FamC)
    (f : X →r famC_base U) (g : Y →r X)
  : FamF U[f][g] U[f ∘r g] :=
  {| famF_base := id_resp (X := Y)
   ; famF_fam x := id_resp (X := U (f (g x))) |}.
Next Obligation. simpl. apply transpS_witness_independent. Defined.

Definition fam_reindex_comp_iso {X Y : SetC} (U : FamC)
    (f : X →r famC_base U) (g : Y →r X)
  : U[f][g] ≅[FamCat] U[f ∘r g].
Proof.
  exists (fam_reindex_comp U f g).
  unshelve notypeclasses refine (({| famF_base := _; famF_fam := _ |}); _).
  - exact (id_resp (X := Y)).
  - exact (λ x, id_resp (X := U (f (g x)))).
  - intros x y p a. simpl. apply transpS_witness_independent.
  - split; exists (λ x, reflS (x := x)); intros x a; apply transpS_id.
Defined.

(** The comparison preserves the canonical morphism into the original family. *)
Theorem fam_reindex_comp_comm {X Y : SetC} (U : FamC)
    (f : X →r famC_base U) (g : Y →r X)
  : FamFEq (fam_comp (fam_reindex U (f ∘r g)) (fam_reindex_comp U f g))
      (fam_comp (fam_reindex U f) (fam_reindex U[f] g)).
Proof.
  exists (λ x, reflS (x := f (g x))). intros x a. apply transpS_id.
Qed.

(** ** Total-Space Pullbacks *)

(** A cone commuting up to setoid equivalence supplies the transport needed
    to put its second coordinate in the reindexed fiber. *)
Program Definition fam_reindex_pair_resp {X Q : SetC} (U : FamC)
    (f : X →r famC_base U) (q1 : Q →r X) (q2 : Q →r SigS (famC_base U) U)
    (Hq : f ∘ q1 ≈ sig_base_resp U ∘ q2)
  : Q →r SigS X U[f]S :=
  {| func z := (q1 z; transpS U (symmetry (Hq z)) (q2 z).2) |}.
Next Obligation.
  pose (q := λ z, symmetry (Hq z)).
  intros z z' p.
  destruct (@func_proper _ _ q2 z z' p) as [r Hr].
  exists (@func_proper _ _ q1 z z' p).
  change (transpS U (@func_proper _ _ f _ _ (@func_proper _ _ q1 z z' p))
    (transpS U (q z) (q2 z).2) ≈S transpS U (q z') (q2 z').2).
  assert (t : (q2 z).1 ≈S f (q1 z')).
  { transitivity (q2 z').1; [exact r | exact (q z')]. }
  transitivity (transpS U t (q2 z).2).
  - symmetry. apply transpS_comp.
  - transitivity (transpS U (q z') (transpS U r (q2 z).2)).
    + apply transpS_comp.
    + apply func_proper. exact Hr.
Defined.

(** The total-space square of the canonical morphism is a pullback. The
    mediator is transparent; uniqueness uses dependent-sum equivalence. *)
Definition fam_reindex_pullback {X : SetC} (U : FamC) (f : X →r famC_base U)
  : @is_pullback SetCat _ _ _ f (sig_base_resp U)
      (SigS X U[f]S) (sig_base_resp U[f]S)
      (fam_total_resp (fam_reindex U f)).
Proof.
  split.
  - intros [x a]. reflexivity.
  - intros Q q1 q2 Hq. exists (fam_reindex_pair_resp U f q1 q2 Hq). split.
    + split.
      * intros z. reflexivity.
      * intros z. exists (Hq z). apply transpS_inv.
    + intros h [H1 H2] z.
      destruct (H2 z) as [p Hp]. exists (H1 z).
      etransitivity.
      * apply (transpS_comp U p).
      * apply func_proper. exact Hp.
Defined.
