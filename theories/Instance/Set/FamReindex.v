From Cats Require Import Cat.Core Cat.Pullback.
From Cats Require Import Instance.Set.Core Instance.Set.Fam Instance.Set.FamCat.

(** * Reindexing Coherent Families *)

Definition ReindexFamC {X : SetC} (U : FamC) (f : X →r famC_base U) : FamC :=
  {| famC_base := X; famC_fam := ReindexFamS U f |}.

(** The canonical family morphism lies over [f] and is the identity on fibers. *)
Definition fam_reindex {X : SetC} (U : FamC) (f : X →r famC_base U)
  : FamF (ReindexFamC U f) U.
Proof.
  refine (@Build_FamF (ReindexFamC U f) U f
    (λ x, id_resp (X := U (f x))) _).
  intros x y p a. reflexivity.
Defined.

(** A cone commuting up to setoid equivalence supplies the transport needed
    to put its second coordinate in the reindexed fiber. *)
Definition fam_reindex_pair_resp {X Q : SetC} (U : FamC)
    (f : X →r famC_base U) (q1 : Q →r X) (q2 : Q →r SigS (famC_base U) U)
    (Hq : f ∘ q1 ≈ sig_base_resp U ∘ q2)
  : Q →r SigS X (ReindexFamS U f).
Proof.
  assert (q : ∀ z, (q2 z).1 ≈S f (q1 z)).
  { intros z. symmetry. exact (Hq z). }
  unshelve refine (@Build_FunS_resp Q (SigS X (ReindexFamS U f))
    (λ z, (q1 z; transpS U (q z) (q2 z).2)) _).
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
      (SigS X (ReindexFamS U f)) (sig_base_resp (ReindexFamS U f))
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
