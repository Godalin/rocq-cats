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

Definition section_reindex {X Y : SetC} {A : FamS Y}
    (s : SectionS_resp A) (f : X →r Y) : SectionS_resp A[f]S.
Proof.
  refine (@Build_SectionS_resp X A[f]S (λ x, s (f x)) _).
  intros x y p. exact (section_proper s (@func_proper _ _ f x y p)).
Defined.

Definition section_reindex_resp {X Y : SetC} (A : FamS Y) (f : X →r Y)
  : SectionS A →r SectionS A[f]S.
Proof.
  unshelve refine (@Build_FunS_resp (SectionS A) (SectionS A[f]S)
    (λ s, section_reindex s f) _).
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

Definition section_of_total {X Y : SetC} (A : FamS Y) (h : X →r SigS Y A)
  : SectionS_resp A[sig_base_resp A ∘r h]S.
Proof.
  refine (@Build_SectionS_resp X A[sig_base_resp A ∘r h]S (λ x, (h x).2) _).
  intros x y q. destruct (@func_proper _ _ h x y q) as [p Hp].
  change (transpS A (@func_proper _ _ (sig_base_resp A ∘r h) x y q)
    (h x).2 ≈S (h y).2).
  transitivity (transpS A p (h x).2).
  - apply transpS_witness_independent.
  - exact Hp.
Defined.

Definition section_var {X : SetC} (A : FamS X)
  : SectionS_resp A[sig_base_resp A]S.
Proof.
  refine (@Build_SectionS_resp (SigS X A) A[sig_base_resp A]S (λ a, a.2) _).
  intros a b [p Hp]. exact Hp.
Defined.

Definition section_pair_universal {X Y : SetC} (A : FamS Y) (f : X →r Y)
    (s : SectionS_resp A[f]S)
  : ∃ h : X →r SigS Y A,
      is_unique (λ h : X →r SigS Y A, ∃ p : sig_base_resp A ∘ h ≈ f,
        ∀ x, transpS A (p x) (h x).2 ≈S s x) h.
Proof.
  unshelve eexists (@Build_FunS_resp X (SigS Y A) (λ x, (f x; s x)) _).
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
