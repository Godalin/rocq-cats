From Cats Require Import Cat.Core Instance.Set.Core Instance.Set.Fam.

(** * Coherent Sections of Families

    A section chooses an element in each fiber and preserves base equivalence
    through the family's transport. Section equality compares these elements
    pointwise, without comparing the proofs of respectfulness. *)

Record SectionS_resp {X : SetC} (A : FamS X) :=
  { section :> ∀ x : X, A x
  ; section_proper {x y : X} (p : x ≈S y)
    : transpS A p (section x) ≈S section y
  }.

Arguments section {_ _} _ _.
Arguments section_proper {_ _} _ {_ _} _.

Definition SectionEq {X : SetC} {A : FamS X} (s t : SectionS_resp A)
  := ∀ x, s x ≈S t x.

Infix "≈s" := SectionEq (at level 50, no associativity) : cat_scope.

Global Instance SectionEq_Equivalence {X A} : Equivalence (@SectionEq X A).
Proof.
  split.
  - intros s x. reflexivity.
  - intros s t H x. symmetry. exact (H x).
  - intros s t u Hst Htu x. transitivity (t x); [apply Hst | apply Htu].
Qed.

Program Canonical SectionS {X : SetC} (A : FamS X) : SetC :=
  {| carrier := SectionS_resp A; carrier_equiv := SectionEq |}.

(** ** Reindexing Sections *)

Program Definition section_reindex {X Y : SetC} {A : FamS Y}
    (s : SectionS_resp A) (f : X →r Y) : SectionS_resp A[f]S :=
  {| section x := s (f x) |}.
Next Obligation. exact (section_proper s (@func_proper _ _ f x y p)). Defined.

Program Definition section_reindex_resp {X Y : SetC} (A : FamS Y) (f : X →r Y)
  : SectionS A →r SectionS A[f]S := {| func s := section_reindex s f |}.
Next Obligation.
  intros s t H x. exact (H (f x)).
Defined.

(** These laws compare values in the same fiber. They do not assert equality
    of the differently indexed family records or their coherence proofs. *)
Theorem section_reindex_id {X : SetC} {A : FamS X} (s : SectionS_resp A) (x : X)
  : section_reindex s (id_resp (X := X)) x ≈S s x.
Proof. reflexivity. Qed.

Theorem section_reindex_comp {X Y Z : SetC} {A : FamS Z}
    (s : SectionS_resp A) (f : Y →r Z) (g : X →r Y) (x : X)
  : section_reindex (section_reindex s f) g x ≈S section_reindex s (f ∘r g) x.
Proof. reflexivity. Qed.

(** ** Generic Element and Pairing

    Over the total space, the second coordinate is a section of the family
    reindexed along its projection. A base map and a section of its reindexed
    family determine a unique map into the total space. *)

Program Definition section_of_total {X Y : SetC} (A : FamS Y) (h : X →r SigS Y A)
  : SectionS_resp A[sig_base_resp A ∘r h]S := {| section x := (h x).2 |}.
Next Obligation.
  destruct (@func_proper _ _ h x y p) as [q Hq].
  change (transpS A (@func_proper _ _ (sig_base_resp A ∘r h) x y p)
    (h x).2 ≈S (h y).2).
  transitivity (transpS A q (h x).2).
  - apply transpS_witness_independent.
  - exact Hq.
Defined.

Program Definition section_var {X : SetC} (A : FamS X)
  : SectionS_resp A[sig_base_resp A]S := {| section a := a.2 |}.
Next Obligation. destruct p as [q Hq]. exact Hq. Defined.

Definition section_pair_universal {X Y : SetC} (A : FamS Y) (f : X →r Y)
    (s : SectionS_resp A[f]S)
  : ∃ h : X →r SigS Y A,
      is_unique (λ h : X →r SigS Y A, ∃ p : sig_base_resp A ∘ h ≈ f,
        ∀ x, transpS A (p x) (h x).2 ≈S s x) h.
Proof.
  unshelve notypeclasses refine (({| func := _ |}); _).
  - exact (λ x, (f x; s x)).
  - intros x y p. exists (@func_proper _ _ f x y p). exact (section_proper s p).
  - split.
    + exists (λ x, reflS (x := f x)). intros x. apply transpS_id.
    + intros h [p Hp] x. exists (p x). exact (Hp x).
Defined.

Definition section_pair_resp {X Y : SetC} (A : FamS Y) (f : X →r Y)
    (s : SectionS_resp A[f]S) : X →r SigS Y A :=
  (section_pair_universal A f s).1.

Global Instance section_pair_proper {X Y : SetC} (A : FamS Y) (f : X →r Y)
  : Proper (SectionEq ==> FunEq) (section_pair_resp A f).
Proof.
  intros s t H x. exists (reflS (x := f x)).
  transitivity (s x); [apply transpS_id | exact (H x)].
Qed.

Theorem section_pair_β1 {X Y : SetC} (A : FamS Y) (f : X →r Y)
    (s : SectionS_resp A[f]S)
  : sig_base_resp A ∘ section_pair_resp A f s ≈ f.
Proof. intros x. reflexivity. Qed.

Theorem section_pair_β2 {X Y : SetC} (A : FamS Y) (f : X →r Y)
    (s : SectionS_resp A[f]S) (x : X)
  : section_var A (section_pair_resp A f s x) ≈S s x.
Proof. reflexivity. Qed.

Theorem section_pair_η {X Y : SetC} (A : FamS Y) (h : X →r SigS Y A)
  : h ≈ section_pair_resp A (sig_base_resp A ∘r h) (section_of_total A h).
Proof.
  intros x. change (h x ≈ΣS ((h x).1; (h x).2)).
  destruct (h x) as [y a]. reflexivity.
Qed.

(** ** Sections of Projections

    A categorical section retains a right-inverse witness. Its equality
    compares the underlying maps, independently of the chosen witnesses. *)

Definition SectionOfEq {X Y : SetC} (p : X →r Y)
    (s t : ∃ r : Y →r X, (p ∘r r) ≈f id_resp) := s.1 ≈f t.1.

Global Instance SectionOfEq_Equivalence {X Y : SetC} (p : X →r Y)
  : Equivalence (SectionOfEq p).
Proof.
  split.
  - intros s x. reflexivity.
  - intros s t H x. symmetry. exact (H x).
  - intros s t u Hst Htu x. transitivity (t.1 x); [apply Hst | apply Htu].
Qed.

Definition SectionOfS {X Y : SetC} (p : X →r Y) : SetC :=
  {| carrier := ∃ s : Y →r X, (p ∘r s) ≈f id_resp
   ; carrier_equiv := SectionOfEq p
   ; carrier_setoid := SectionOfEq_Equivalence p |}.

Notation "'Sec(' p ')'" := (SectionOfS p) (format "Sec( p )") : cat_scope.

Program Definition section_to_projection_resp {X : SetC} (A : FamS X)
  : SectionS A →r Sec(sig_base_resp A) :=
  {| func s := (section_pair_resp A (id_resp (X := X)) (section_reindex s id_resp);
      section_pair_β1 A id_resp (section_reindex s id_resp)) |}.
Next Obligation.
  intros s t H x. exists (reflS (x := x)).
  transitivity (s x); [apply transpS_id | exact (H x)].
Defined.

(** The image of a categorical section may lie over a representative only
    equivalent to its argument. Its right-inverse witness supplies the transport. *)
Program Definition section_from_projection {X : SetC} (A : FamS X)
    (s : Sec(sig_base_resp A)) : SectionS_resp A :=
  {| section x := transpS A (s.2 x) (s.1 x).2 |}.
Next Obligation.
  destruct (@func_proper _ _ s.1 x y p) as [q Hq].
  assert (r : (s.1 x).1 ≈S y).
  { transitivity x; [exact (s.2 x) | exact p]. }
  transitivity (transpS A r (s.1 x).2).
  - symmetry. apply transpS_comp.
  - transitivity (transpS A (s.2 y) (transpS A q (s.1 x).2)).
    + apply transpS_comp.
    + apply func_proper. exact Hq.
Defined.

Program Definition section_from_projection_resp {X : SetC} (A : FamS X)
  : Sec(sig_base_resp A) →r SectionS A := {| func := section_from_projection A |}.
Next Obligation.
  intros s t H x. destruct (H x) as [p Hp].
  change (transpS A (s.2 x) (s.1 x).2 ≈S transpS A (t.2 x) (t.1 x).2).
  transitivity (transpS A (t.2 x) (transpS A p (s.1 x).2)).
  - apply transpS_comp.
  - apply func_proper. exact Hp.
Defined.

Definition section_projection_iso {X : SetC} (A : FamS X)
  : SectionS A ≅[SetCat] Sec(sig_base_resp A).
Proof.
  exists (section_to_projection_resp A), (section_from_projection_resp A). split.
  - intros s x. apply transpS_id.
  - intros s x.
    change ((x; transpS A (s.2 x) (s.1 x).2) ≈ΣS s.1 x).
    assert (p : x ≈S (s.1 x).1) by (symmetry; exact (s.2 x)).
    exists p. apply transpS_inv.
Defined.
