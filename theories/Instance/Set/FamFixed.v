From Cats Require Import Cat.Core Cat.Functor Cat.Natural.
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

Infix "∘Fam" := fam_map_comp
  (at level 40, left associativity) : cat_scope.

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

(** Identity and composite substitution retain the same fiber values;
    their transport witnesses are compared by coherence. *)
Program Definition fam_map_reindex_id {X : SetC} (A : FamS X)
  : A →Fam A[id_resp]S := {| fam_map x := id_resp |}.
Next Obligation. apply transpS_witness_independent. Defined.

Definition fam_map_reindex_id_iso {X : SetC} (A : FamS X)
  : @is_iso (FamSCat X) _ _ (fam_map_reindex_id A).
Proof.
  unshelve notypeclasses refine (({| fam_map := _ |}); _).
  - exact (λ x, id_resp).
  - intros x y p a. cbn. apply transpS_witness_independent.
  - split; intros x a; reflexivity.
Defined.

Program Definition FamReindexIdN (X : SetC)
  : (@IdF (FamSCat X)) => (FamReindexF (id_resp (X := X))) :=
  {| nt := fam_map_reindex_id |}.
Next Obligation. intros x a. reflexivity. Defined.

Definition fam_reindex_id_nat_iso (X : SetC)
  : (@IdF (FamSCat X)) ≅N (FamReindexF (id_resp (X := X))) :=
  (FamReindexIdN X; fam_map_reindex_id_iso).

Program Definition fam_map_reindex_comp {X Y Z : SetC}
    (f : Y →r Z) (g : X →r Y) (A : FamS Z)
  : A[f]S[g]S →Fam A[f ∘r g]S := {| fam_map x := id_resp |}.
Next Obligation. apply transpS_witness_independent. Defined.

Notation "A '⟨' f ',' g '⟩Fam'" := (fam_map_reindex_comp f g A)
  (at level 8, left associativity, format "A ⟨ f ,  g ⟩Fam") : cat_scope.

Definition fam_map_reindex_comp_iso {X Y Z : SetC}
    (f : Y →r Z) (g : X →r Y) (A : FamS Z)
  : @is_iso (FamSCat X) _ _ A⟨f, g⟩Fam.
Proof.
  unshelve notypeclasses refine (({| fam_map := _ |}); _).
  - exact (λ x, id_resp).
  - intros x y p a. cbn. apply transpS_witness_independent.
  - split; intros x a; reflexivity.
Defined.

Program Definition FamReindexCompN {X Y Z : SetC} (f : Y →r Z) (g : X →r Y)
  : (FamReindexF g ∘F FamReindexF f) => (FamReindexF (f ∘r g)) :=
  {| nt := fam_map_reindex_comp f g |}.
Next Obligation. intros x a. reflexivity. Defined.

Definition fam_reindex_comp_nat_iso {X Y Z : SetC} (f : Y →r Z) (g : X →r Y)
  : (FamReindexF g ∘F FamReindexF f) ≅N (FamReindexF (f ∘r g)) :=
  (FamReindexCompN f g; fam_map_reindex_comp_iso f g).

(** ** Equivalent Substitutions and Coherence

    Base-map equivalences act by transport. Their witnesses are retained,
    while the resulting maps are independent of the chosen witness. *)
Program Definition fam_map_reindex_equiv {X Y : SetC} {f g : X →r Y}
    (H : f ≈f g) (A : FamS Y) : A[f]S →Fam A[g]S :=
  {| fam_map x := transpS A (H x) |}.
Next Obligation.
  transitivity (transpS A (transitivity (@func_proper _ _ f x y p) (H y)) a).
  - symmetry. apply transpS_comp.
  - apply transpS_comp.
Defined.

Notation "A '⟦' H '⟧Fam'" := (fam_map_reindex_equiv H A)
  (at level 8, left associativity, format "A ⟦ H ⟧Fam") : cat_scope.

Definition fam_map_reindex_equiv_iso {X Y : SetC} {f g : X →r Y}
    (H : f ≈f g) (A : FamS Y) : @is_iso (FamSCat X) _ _ A⟦H⟧Fam.
Proof.
  exists A⟦symmetry H⟧Fam. split; intros x a; cbn.
  - transitivity (transpS A (reflS (x := f x)) a).
    + symmetry. apply transpS_comp.
    + apply transpS_id.
  - transitivity (transpS A (reflS (x := g x)) a).
    + symmetry. apply transpS_comp.
    + apply transpS_id.
Defined.

Program Definition FamReindexEqN {X Y : SetC} {f g : X →r Y} (H : f ≈f g)
  : FamReindexF f => FamReindexF g := {| nt := fam_map_reindex_equiv H |}.
Next Obligation.
  intros x a. cbn. symmetry. exact (fam_map_naturality f0 (H x) a).
Defined.

Definition fam_reindex_equiv_nat_iso {X Y : SetC} {f g : X →r Y} (H : f ≈f g)
  : FamReindexF f ≅N FamReindexF g :=
  (FamReindexEqN H; fam_map_reindex_equiv_iso H).

Global Instance FamReindexF_proper {X Y : SetC}
  : Proper (@HomEq SetCat X Y ==> NatIso) (@FamReindexF X Y).
Proof. intros f g H. exact (fam_reindex_equiv_nat_iso H). Defined.

Theorem fam_reindex_equiv_witness_independent {X Y : SetC} {f g : X →r Y}
    (H K : f ≈f g) : FamReindexEqN H ≈N FamReindexEqN K.
Proof. intros A x a. cbn. apply transpS_witness_independent. Qed.

Theorem fam_reindex_equiv_id {X Y : SetC} {f : X →r Y} (H : f ≈f f)
  : FamReindexEqN H ≈N idN.
Proof. intros A x a. cbn. apply transpS_id. Qed.

Theorem fam_reindex_equiv_comp {X Y : SetC} {f g h : X →r Y}
    (H : f ≈f g) (K : g ≈f h) (L : f ≈f h)
  : FamReindexEqN L ≈N (FamReindexEqN K ∘Nv FamReindexEqN H).
Proof. intros A x a. cbn. apply transpS_comp. Qed.

(** The composition comparison is natural in both base maps. Any witness
    of the composite equivalence gives the same comparison. *)
Theorem fam_reindex_comp_equiv {X Y Z : SetC} {f f' : Y →r Z} {g g' : X →r Y}
    (H : f ≈f f') (K : g ≈f g') (L : (f ∘r g) ≈f (f' ∘r g')) (A : FamS Z)
  : A⟦L⟧Fam ∘Fam A⟨f, g⟩Fam ≈Fam
      A⟨f', g'⟩Fam ∘Fam A[f']S⟦K⟧Fam ∘Fam
        fam_map_reindex g A⟦H⟧Fam.
Proof. intros x a. cbn. apply transpS_comp. Qed.

(** Unit and associativity diagrams are stated after aligning their base
    maps by equivalence; no equality of substitution records is used. *)
Theorem fam_reindex_unit_l {X Y : SetC} (f : X →r Y)
    (H : (id_resp ∘r f) ≈f f) (A : FamS Y)
  : A⟦H⟧Fam ∘Fam A⟨id_resp, f⟩Fam ∘Fam
      fam_map_reindex f (fam_map_reindex_id A) ≈Fam fam_map_id A[f]S.
Proof. intros x a. cbn. apply transpS_id. Qed.

Theorem fam_reindex_unit_r {X Y : SetC} (f : X →r Y)
    (H : (f ∘r id_resp) ≈f f) (A : FamS Y)
  : A⟦H⟧Fam ∘Fam A⟨f, id_resp⟩Fam ∘Fam
      fam_map_reindex_id A[f]S ≈Fam fam_map_id A[f]S.
Proof. intros x a. cbn. apply transpS_id. Qed.

Theorem fam_reindex_assoc {X Y Z W : SetC}
    (f : Z →r W) (g : Y →r Z) (h : X →r Y)
    (H : ((f ∘r g) ∘r h) ≈f (f ∘r (g ∘r h))) (A : FamS W)
  : A⟦H⟧Fam ∘Fam A⟨f ∘r g, h⟩Fam ∘Fam
      fam_map_reindex h A⟨f, g⟩Fam ≈Fam
    A⟨f, g ∘r h⟩Fam ∘Fam A[f]S⟨g, h⟩Fam.
Proof. intros x a. cbn. apply transpS_id. Qed.
