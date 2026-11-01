From Cats Require Import Cat.Core Cat.Functor Cat.Fibration.
From Cats Require Import Instance.Set.Core Instance.Set.Fam.Core Instance.Set.Fam.Cat
  Instance.Set.Fam.Reindex.

(** * Cartesian Lifts of Coherent Families *)

Program Definition fam_reindex_factor {X : SetC} (U : FamC) (f : X →r famC_base U)
    {V : FamC} (g : FamF V U) (u : famC_base V →r X)
    (H : (f ∘r u) ≈f famF_base g) : FamF V U[f] :=
  {| famF_base := u
   ; famF_fam x := transpS U (symmetry (H x)) ∘r famF_fam g x |}.
Next Obligation.
  pose (q := λ x, symmetry (H x)).
  change (transpS U (q y) (famF_fam g y (transpS V p a)) ≈S
    transpS U (@func_proper _ _ f _ _ (@func_proper _ _ u x y p))
      (transpS U (q x) (famF_fam g x a))).
  pose (r := @func_proper _ _ (famF_base g) x y p).
  assert (t : famF_base g x ≈S f (u y)).
  { transitivity (famF_base g y); [exact r | exact (q y)]. }
  transitivity (transpS U (q y) (transpS U r (famF_fam g x a))).
  - apply func_proper. apply famF_naturality.
  - transitivity (transpS U t (famF_fam g x a)).
    + symmetry. apply transpS_comp.
    + apply transpS_comp.
Defined.

(** Reindexing is universal among family morphisms above a specified base
    factor. Uniqueness retains base equivalence and compares fibers by transport. *)
Definition fam_reindex_cartesian {X : SetC} (U : FamC) (f : X →r famC_base U)
  : fam_reindex U f ⦂ Cart(FamBaseF).
Proof.
  intros V g u H. exists (fam_reindex_factor U f g u H). split.
  - split.
    + intros x. reflexivity.
    + exists H. intros x a. apply transpS_inv.
  - intros h [Hbase [p Hp]]. exists Hbase. intros x a.
    cbn [fam_reindex_factor famF_fam comp_resp func].
    etransitivity.
    + apply (transpS_comp U (p x)).
    + apply func_proper. exact (Hp x a).
Defined.

(** This chosen structure is enabled explicitly by clients. Its base-object
    identification is reflexive, and its underlying arrow is [fam_reindex]. *)
Program Definition FamBaseF_HasCartesianLift : HasCartesianLift FamBaseF :=
  {| CartesianLift U X f := U[f]
   ; cartesian_lift_base U X f := eq_refl
   ; cartesian_lift U X f := fam_reindex U f |}.
Next Obligation. intros x. reflexivity. Defined.
Next Obligation. apply fam_reindex_cartesian. Defined.

(** ** Reindexing Family Morphisms

    The direct construction preserves the computation on fibers. Its
    universal characterization agrees with the abstract cartesian factor. *)
Program Definition fam_reindex_map {X : SetC} {U V : FamC} (φ : FamF U V)
    (f : X →r famC_base U) : FamF U[f] V[famF_base φ ∘r f] :=
  {| famF_base := id_resp (X := X)
   ; famF_fam x := famF_fam φ (f x) |}.
Next Obligation.
  change (famF_fam φ (f y) (transpS U (@func_proper _ _ f x y p) a) ≈S
    transpS V (@func_proper _ _ (famF_base φ ∘r f) x y
      (@func_proper _ _ (id_resp (X := X)) x y p)) (famF_fam φ (f x) a)).
  etransitivity. apply famF_naturality. apply transpS_witness_independent.
Defined.

Notation "φ '⟦' f '⟧'" := (fam_reindex_map φ f)
  (at level 8, left associativity, format "φ ⟦ f ⟧") : cat_scope.

Theorem fam_reindex_map_comm {X : SetC} {U V : FamC} (φ : FamF U V)
    (f : X →r famC_base U)
  : FamFEq (fam_comp (fam_reindex V (famF_base φ ∘r f)) φ⟦f⟧)
      (fam_comp φ (fam_reindex U f)).
Proof.
  exists (λ x, reflS (x := famF_base φ (f x))). intros x a. apply transpS_id.
Qed.

Theorem fam_reindex_map_factor {X : SetC} {U V : FamC} (φ : FamF U V)
    (f : X →r famC_base U)
    (H : fmap FamBaseF (fam_reindex V (famF_base φ ∘r f)) ∘ id
      ≈ fmap FamBaseF (fam_comp φ (fam_reindex U f)))
  : FamFEq φ⟦f⟧
      (cartesian_factor (fam_reindex_cartesian V (famF_base φ ∘r f))
        (fam_comp φ (fam_reindex U f)) id H).
Proof.
  apply (that _ _ (cartesian_factor_unique
    (fam_reindex_cartesian V (famF_base φ ∘r f))
    (fam_comp φ (fam_reindex U f)) id H)). split.
  - intros x. reflexivity.
  - apply fam_reindex_map_comm.
Qed.
