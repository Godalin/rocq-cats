From Cats Require Import Cat.Core Cat.Functor.
From Cats Require Import Instance.Set.Core Instance.Set.Fam Instance.Set.FamCat.

(** * Coherent Families over a Fixed Setoid

    Morphisms stay in each fiber and commute with transport. Their equality
    compares values, without comparing respectfulness or coherence proofs. *)

Record FamMap {X : SetC} (A B : FamS X) :=
  { fam_map (x : X) : A x →r B x
  ; fam_map_naturality {x y : X} (p : x ≈S y) (a : A x)
    : fam_map y (transpS A p a) ≈S transpS B p (fam_map x a)
  }.

Arguments fam_map {_ _ _} _ _.
Arguments fam_map_naturality {_ _ _} _ {_ _} _ _.

Infix "→Fam" := FamMap (at level 99) : cat_scope.

Definition FamMapEq {X : SetC} {A B : FamS X} (f g : A →Fam B)
  := ∀ x, fam_map f x ≈f fam_map g x.

Infix "≈Fam" := FamMapEq (at level 50) : cat_scope.

Global Instance FamMapEq_Equivalence {X : SetC} {A B : FamS X}
  : Equivalence (@FamMapEq X A B).
Proof.
  split.
  - intros f x a. reflexivity.
  - intros f g H x a. symmetry. exact (H x a).
  - intros f g h Hfg Hgh x a. transitivity (fam_map g x a).
    + exact (Hfg x a).
    + exact (Hgh x a).
Qed.

Program Definition fam_map_id {X : SetC} (A : FamS X) : A →Fam A :=
  {| fam_map x := id_resp |}.
Next Obligation. reflexivity. Defined.

Program Definition fam_map_comp {X : SetC} {A B D : FamS X}
    (g : B →Fam D) (f : A →Fam B) : A →Fam D :=
  {| fam_map x := fam_map g x ∘r fam_map f x |}.
Next Obligation.
  rewrite (fam_map_naturality f p), (fam_map_naturality g p). reflexivity.
Defined.

Program Definition FamSCat (X : SetC) : Cat :=
  {| Ob := FamS X
   ; Hom := FamMap
   ; HomEq A B := FamMapEq
   ; id := fam_map_id
   ; comp A B D := fam_map_comp
   |}.
Next Obligation.
  intros g g' Hg f f' Hf x a. cbn.
  transitivity (fam_map g x (fam_map f' x a)).
  - apply func_proper. exact (Hf x a).
  - exact (Hg x (fam_map f' x a)).
Defined.
Next Obligation. intros x a. reflexivity. Defined.
Next Obligation. intros x a. reflexivity. Defined.
Next Obligation. intros x a. reflexivity. Defined.

(** Relate fixed-base maps to the existing category of all families. *)
Definition FixedFamC {X : SetC} (A : FamS X) : FamC :=
  {| famC_base := X; famC_fam := A |}.

Program Definition fam_map_to_fam {X : SetC} {A B : FamS X} (f : A →Fam B)
  : FamF (FixedFamC A) (FixedFamC B) :=
  {| famF_base := id_resp
   ; famF_fam := fam_map f |}.
Next Obligation.
  transitivity (transpS B p (fam_map f x a)).
  - apply fam_map_naturality.
  - apply transpS_witness_independent.
Defined.

Program Definition FamFixedF (X : SetC) : Functor (FamSCat X) FamCat :=
  {| F0 := FixedFamC
   ; F1 A B := fam_map_to_fam |}.
Next Obligation.
  intros f g H. exists (λ x, reflS (x := x)). intros x a.
  transitivity (fam_map f x a); [apply transpS_id | exact (H x a)].
Defined.
Next Obligation.
  exists (λ x, reflS (x := x)). intros x a. apply transpS_id.
Defined.
Next Obligation.
  exists (λ x, reflS (x := x)). intros x a. apply transpS_id.
Defined.

Definition fam_map_total_resp {X : SetC} {A B : FamS X} (f : A →Fam B)
  : SigS X A →r SigS X B := fam_total_resp (fam_map_to_fam f).

(** Substitution is already available on families; extend it to maps. *)
Program Definition fam_map_reindex {X Y : SetC} {A B : FamS Y}
    (f : X →r Y) (φ : A →Fam B) : A[f]S →Fam B[f]S :=
  {| fam_map x := fam_map φ (f x) |}.
Next Obligation. apply fam_map_naturality. Defined.

Program Definition FamReindexF {X Y : SetC} (f : X →r Y)
  : Functor (FamSCat Y) (FamSCat X) :=
  {| F0 A := A[f]S
   ; F1 A B := fam_map_reindex f |}.
Next Obligation. intros φ ψ H x a. exact (H (f x) a). Defined.
Next Obligation. intros x a. reflexivity. Defined.
Next Obligation. intros x a. reflexivity. Defined.
