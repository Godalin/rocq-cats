From Cats Require Import Cat.Core Cat.Functor Cat.Terminal.
From Cats Require Import Instance.Set.Fam Instance.Set.FamCat.

(** * Categories with Families

    Context homs, types and terms use the same foundational [SetC] and its
    specified equality. A family-valued presheaf carries types, terms and
    coherent conversion; there are no separate type/term equality fields. *)

Section TypesAndTerms.
Context {C : Cat} (T : Functor (C^op) FamCat).

Definition Ty (Γ : @Ob C) : SetC := famC_base (T Γ).
Definition Tm (Γ : @Ob C) : FamS (Ty Γ) := famC_fam (T Γ).

Definition ty_sub {Δ Γ : @Ob C} (σ : Hom Δ Γ) : Ty Γ →r Ty Δ :=
  famF_base (fmap T σ).

Definition tm_sub {Δ Γ : @Ob C} (σ : Hom Δ Γ) {A : Ty Γ}
  : Tm Γ A →r Tm Δ (ty_sub σ A) := famF_fam (fmap T σ) A.

Definition tm_conv {Γ : @Ob C} {A B : Ty Γ} (e : A ≈S B)
  : Tm Γ A →r Tm Γ B := transpS (Tm Γ) e.

Definition ty_sub_id {Γ : @Ob C} (A : Ty Γ) : ty_sub id A ≈S A :=
  (functor_id (C^op) FamCat T).1 A.

Definition ty_sub_comp {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (τ : Hom Θ Δ)
    (A : Ty Γ) : ty_sub τ (ty_sub σ A) ≈S ty_sub (σ ∘ τ) A :=
  (symmetry (functor_comp (C^op) FamCat T τ σ)).1 A.

Definition ty_sub_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ} (H : σ ≈ σ')
    (A : Ty Γ) : ty_sub σ A ≈S ty_sub σ' A :=
  (@functor_fmap_proper (C^op) FamCat T Γ Δ σ σ' H).1 A.

Definition ty_sub_comm {Γ Δ Θ : @Ob C} (A : Ty Γ)
    (σ : Hom Δ Γ) (τ : Hom Θ Δ) {ρ : Hom Θ Γ} (H : σ ∘ τ ≈ ρ)
  : ty_sub τ (ty_sub σ A) ≈S ty_sub ρ A :=
  transitivity (ty_sub_comp σ τ A) (ty_sub_equiv H A).

Theorem tm_conv_id {Γ : @Ob C} {A : Ty Γ} (e : A ≈S A) (t : Tm Γ A)
  : tm_conv e t ≈S t.
Proof. apply transpS_id. Qed.

Theorem tm_conv_comp {Γ : @Ob C} {A B D : Ty Γ}
    (e : A ≈S B) (d : B ≈S D) (r : A ≈S D) (t : Tm Γ A)
  : tm_conv r t ≈S tm_conv d (tm_conv e t).
Proof. apply transpS_comp. Qed.

Theorem tm_conv_witness_independent {Γ : @Ob C} {A B : Ty Γ}
    (e d : A ≈S B) : tm_conv e ≈f tm_conv d.
Proof. apply transpS_witness_independent. Qed.

Theorem tm_sub_conv {Γ Δ : @Ob C} (σ : Hom Δ Γ)
    {A B : Ty Γ} (e : A ≈S B) (t : Tm Γ A)
  : tm_sub σ (tm_conv e t) ≈S
    tm_conv (@func_proper _ _ (ty_sub σ) _ _ e) (tm_sub σ t).
Proof. exact (famF_naturality (fmap T σ) e t). Qed.

Theorem tm_sub_id {Γ : @Ob C} {A : Ty Γ} (t : Tm Γ A)
  : tm_conv (ty_sub_id A) (tm_sub id t) ≈S t.
Proof. exact ((functor_id (C^op) FamCat T).2 A t). Qed.

Theorem tm_sub_comp {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (τ : Hom Θ Δ)
    {A : Ty Γ} (t : Tm Γ A)
  : tm_conv (ty_sub_comp σ τ A) (tm_sub τ (tm_sub σ t)) ≈S tm_sub (σ ∘ τ) t.
Proof. exact ((symmetry (functor_comp (C^op) FamCat T τ σ)).2 A t). Qed.

Theorem tm_sub_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ} (H : σ ≈ σ')
    {A : Ty Γ} (t : Tm Γ A)
  : tm_conv (ty_sub_equiv H A) (tm_sub σ t) ≈S tm_sub σ' t.
Proof. exact ((@functor_fmap_proper (C^op) FamCat T Γ Δ σ σ' H).2 A t). Qed.

End TypesAndTerms.

(** The presheaf is explicit in the notation: its object map need not
    determine it uniquely, and candidate properties do not require a CwF. *)
Notation "A '[' σ ']Ty[' T ']'" := (ty_sub T σ A)
  (at level 8, left associativity, format "A [ σ ]Ty[ T ]") : cat_scope.
Notation "t '[' σ ']Tm[' T ']'" := (tm_sub T σ t)
  (at level 8, left associativity, format "t [ σ ]Tm[ T ]") : cat_scope.
Notation "e '▸[' T ']' t" := (tm_conv T e t)
  (at level 40, left associativity, format "e  ▸[ T ]  t") : cat_scope.

(** ** Candidate Context Extensions

    A pairing equation retains the base equality witness. Its second law
    compares terms after composition and base-equality conversion. *)
Section ContextExtension.
Context {C : Cat} (T : Functor (C^op) FamCat).

Definition is_context_pair {Γ E Δ : @Ob C} (A : Ty T Γ) (p : Hom E Γ)
    (q : Tm T E A[p]Ty[T]) (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
    (h : Hom Δ E) :=
  ∃ H : p ∘ h ≈ σ, ty_sub_comm T A p h H ▸[T] q[h]Tm[T] ≈S t.

Definition is_context_extension {Γ : @Ob C} (A : Ty T Γ) (E : @Ob C)
    (p : Hom E Γ) (q : Tm T E A[p]Ty[T]) :=
  ∀ Δ (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T]),
    ∃ h : Hom Δ E, is_unique (is_context_pair A p q σ t) h.

Class HasContextExtension :=
  { Ext {Γ : @Ob C} (A : Ty T Γ) : @Ob C
  ; context_proj {Γ : @Ob C} (A : Ty T Γ) : Hom (Ext A) Γ
  ; context_var {Γ : @Ob C} (A : Ty T Γ) : Tm T (Ext A) A[context_proj A]Ty[T]
  ; context_extension_universal {Γ : @Ob C} (A : Ty T Γ)
    : is_context_extension A (Ext A) (context_proj A) (context_var A)
  }.

Context `{HC : !HasContextExtension}.

Definition context_pair {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T]) : Hom Δ (Ext A) :=
  (context_extension_universal A Δ σ t).1.

Theorem context_pair_universal {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T])
  : is_unique (is_context_pair A (context_proj A) (context_var A) σ t)
      (context_pair A σ t).
Proof. exact (context_extension_universal A Δ σ t).2. Defined.

Definition context_pair_β1 {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T]) : context_proj A ∘ context_pair A σ t ≈ σ :=
  (@this _ _ _ _ _ (context_pair_universal A σ t)).1.

Theorem context_pair_β2 {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T])
  : ty_sub_comm T A (context_proj A) (context_pair A σ t)
      (context_pair_β1 A σ t) ▸[T] (context_var A)[context_pair A σ t]Tm[T] ≈S t.
Proof. exact (@this _ _ _ _ _ (context_pair_universal A σ t)).2. Qed.

Theorem context_pair_unique {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T]) (h : Hom Δ (Ext A))
  : is_context_pair A (context_proj A) (context_var A) σ t h
    → h ≈ context_pair A σ t.
Proof. exact (@that _ _ _ _ _ (context_pair_universal A σ t) h). Qed.

Theorem context_pair_η {Γ Δ : @Ob C} (A : Ty T Γ) (h : Hom Δ (Ext A))
  : h ≈ context_pair A (context_proj A ∘ h)
      (ty_sub_comp T (context_proj A) h A ▸[T] (context_var A)[h]Tm[T]).
Proof.
  apply context_pair_unique. exists (reflexivity (context_proj A ∘ h)).
  apply tm_conv_witness_independent.
Qed.

Theorem context_pair_β2_witness {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T]) (H : context_proj A ∘ context_pair A σ t ≈ σ)
  : ty_sub_comm T A (context_proj A) (context_pair A σ t) H ▸[T]
      (context_var A)[context_pair A σ t]Tm[T] ≈S t.
Proof.
  transitivity (ty_sub_comm T A (context_proj A) (context_pair A σ t)
    (context_pair_β1 A σ t) ▸[T] (context_var A)[context_pair A σ t]Tm[T]).
  - apply tm_conv_witness_independent.
  - apply context_pair_β2.
Qed.

Global Instance context_pair_proper {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
  : Proper (carrier_equiv (Tm T Δ A[σ]Ty[T]) ==> HomEq) (context_pair A σ).
Proof.
  intros t u H. apply context_pair_unique. exists (context_pair_β1 A σ t).
  transitivity t; [apply context_pair_β2 | exact H].
Qed.

Theorem context_pair_equiv {Γ Δ : @Ob C} (A : Ty T Γ) {σ σ' : Hom Δ Γ}
    (H : σ ≈ σ') (t : Tm T Δ A[σ]Ty[T]) (u : Tm T Δ A[σ']Ty[T])
  : ty_sub_equiv T H A ▸[T] t ≈S u → context_pair A σ t ≈ context_pair A σ' u.
Proof.
  intros Htu. apply context_pair_unique.
  exists (transitivity (context_pair_β1 A σ t) H).
  transitivity (ty_sub_equiv T H A ▸[T] t).
  - transitivity (ty_sub_equiv T H A ▸[T]
      (ty_sub_comm T A (context_proj A) (context_pair A σ t)
        (context_pair_β1 A σ t) ▸[T] (context_var A)[context_pair A σ t]Tm[T])).
    + apply tm_conv_comp.
    + apply func_proper. apply context_pair_β2.
  - exact Htu.
Qed.

End ContextExtension.

Notation "Γ '▹[' T ']' A" := (Ext T (Γ := Γ) A)
  (at level 40, left associativity, format "Γ  ▹[ T ]  A") : cat_scope.
Notation "'⟨' σ ';' t '⟩[' T ',' A ']'" := (context_pair T A σ t)
  (at level 0, format "⟨ σ ;  t ⟩[ T ,  A ]") : cat_scope.

(** Like [CCC] and [ETCS], an enabled bundle supplies its substructures.
    Concrete CwF models still have to be enabled explicitly. *)
Class CwF (C : Cat) :=
  { hasTerminal :: HasTerminal C
  ; TyTmF : Functor (C^op) FamCat
  ; hasContextExtension :: HasContextExtension TyTmF
  }.

Arguments TyTmF {_} _.
