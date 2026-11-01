From Cats Require Import Cat.Core Cat.Functor Cat.Section.
From Cats Require Import DTT.CwF DTT.ContextExtension.
From Cats Require Import DTT.ContextPullback.
From Cats Require Import Instance.Set.Core Instance.Set.Fam Instance.Set.FamCat.

(** * Terms as Sections of Context Projections *)

Section ContextSections.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Program Definition term_to_section_resp {Γ : @Ob C} (A : Ty T Γ)
  : Tm T Γ A →r Sec(context_proj T A) :=
  {| func t := (⟨id; symmetry (ty_sub_id T A) ▸[T] t⟩[T, A];
      context_pair_β1 T A id (symmetry (ty_sub_id T A) ▸[T] t)) |}.
Next Obligation.
  intros t u H. apply context_pair_proper. apply func_proper. exact H.
Defined.

Program Definition section_to_term_resp {Γ : @Ob C} (A : Ty T Γ)
  : Sec(context_proj T A) →r Tm T Γ A :=
  {| func s := transitivity (ty_sub_comm T A (context_proj T A) s.1 s.2)
      (ty_sub_id T A) ▸[T] (context_var T A)[s.1]Tm[T] |}.
Next Obligation.
  intros s t H.
  transitivity (transitivity (ty_sub_comm T A (context_proj T A) t.1 t.2)
    (ty_sub_id T A) ▸[T]
      (ty_sub_equiv T H A[context_proj T A]Ty[T] ▸[T]
        (context_var T A)[s.1]Tm[T])).
  - apply tm_conv_comp.
  - apply func_proper. apply tm_sub_equiv.
Defined.

End ContextSections.

Notation "t '^Sec[' T ',' A ']'" := (term_to_section_resp T A t)
  (at level 35, format "t ^Sec[ T ,  A ]") : cat_scope.
Notation "s '^Tm[' T ',' A ']'" := (section_to_term_resp T A s)
  (at level 35, format "s ^Tm[ T ,  A ]") : cat_scope.

Section ContextSectionLaws.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Theorem term_section_β {Γ : @Ob C} (A : Ty T Γ) (t : Tm T Γ A)
  : t^Sec[T, A]^Tm[T, A] ≈S t.
Proof.
  cbn.
  transitivity (ty_sub_id T A ▸[T]
    (ty_sub_comm T A (context_proj T A)
      ⟨id; symmetry (ty_sub_id T A) ▸[T] t⟩[T, A]
      (context_pair_β1 T A id (symmetry (ty_sub_id T A) ▸[T] t))
      ▸[T] (context_var T A)[⟨id; symmetry (ty_sub_id T A) ▸[T] t⟩[T, A]]Tm[T])).
  - apply tm_conv_comp.
  - transitivity (ty_sub_id T A ▸[T] (symmetry (ty_sub_id T A) ▸[T] t)).
    + apply func_proper. apply context_pair_β2.
    + transitivity (reflexivity A ▸[T] t).
      * symmetry. apply tm_conv_comp.
      * apply tm_conv_id.
Defined.

Theorem term_section_η {Γ : @Ob C} (A : Ty T Γ) (s : Sec(context_proj T A))
  : s^Tm[T, A]^Sec[T, A] ≈S s.
Proof.
  change (⟨id; symmetry (ty_sub_id T A) ▸[T]
      (transitivity (ty_sub_comm T A (context_proj T A) s.1 s.2)
        (ty_sub_id T A) ▸[T] (context_var T A)[s.1]Tm[T])⟩[T, A] ≈ s.1).
  transitivity ⟨id; ty_sub_comm T A (context_proj T A) s.1 s.2
    ▸[T] (context_var T A)[s.1]Tm[T]⟩[T, A].
  - apply context_pair_proper. symmetry. apply tm_conv_comp.
  - symmetry. apply context_pair_η_base.
Defined.

Definition context_term_section_iso {Γ : @Ob C} (A : Ty T Γ)
  : Tm T Γ A ≅[SetCat] Sec(context_proj T A).
Proof.
  exists (term_to_section_resp T A), (section_to_term_resp T A). split.
  - intros t. apply term_section_β.
  - intros s. apply term_section_η.
Defined.

(** Pairing is the substituted section. *)
Theorem term_section_pair {Γ Δ : @Ob C} (A : Ty T Γ) (t : Tm T Γ A)
    (σ : Hom Δ Γ)
  : (t^Sec[T, A]).1 ∘ σ ≈ ⟨σ; t[σ]Tm[T]⟩[T, A].
Proof.
  transitivity ⟨id ∘ σ; ty_sub_comp T id σ A
    ▸[T] (symmetry (ty_sub_id T A) ▸[T] t)[σ]Tm[T]⟩[T, A].
  - apply context_pair_comp.
  - apply (context_pair_equiv T A (comp_id_l σ)).
    transitivity (ty_sub_equiv T (comp_id_l σ) A ▸[T]
      (ty_sub_comp T id σ A ▸[T]
        ((symmetry (ty_sub_id T A))[σ]Eq[T] ▸[T] t[σ]Tm[T]))).
    + apply func_proper. apply func_proper. apply tm_sub_conv.
    + transitivity (transitivity (symmetry (ty_sub_id T A))[σ]Eq[T]
        (transitivity (ty_sub_comp T id σ A) (ty_sub_equiv T (comp_id_l σ) A))
        ▸[T] t[σ]Tm[T]).
      * transitivity (ty_sub_equiv T (comp_id_l σ) A ▸[T]
          (transitivity (symmetry (ty_sub_id T A))[σ]Eq[T]
            (ty_sub_comp T id σ A) ▸[T] t[σ]Tm[T])).
        -- apply func_proper. symmetry. apply tm_conv_comp.
        -- symmetry. apply tm_conv_comp.
      * apply tm_conv_id.
Qed.

(** Substitution of terms agrees with pullback of their sections. *)
Theorem term_section_sub {Γ Δ : @Ob C} (A : Ty T Γ) (t : Tm T Γ A)
    (σ : Hom Δ Γ)
  : σ^+[T, A] ∘ (t[σ]Tm[T]^Sec[T, A[σ]Ty[T]]).1 ≈ (t^Sec[T, A]).1 ∘ σ.
Proof.
  transitivity ⟨σ ∘ id; ty_sub_comp T σ id A
    ▸[T] (symmetry (ty_sub_id T A[σ]Ty[T]) ▸[T] t[σ]Tm[T])⟩[T, A].
  - apply context_lift_pair.
  - transitivity ⟨σ; t[σ]Tm[T]⟩[T, A].
    + apply (context_pair_equiv T A (comp_id_r σ)).
      transitivity (ty_sub_equiv T (comp_id_r σ) A ▸[T]
        (transitivity (symmetry (ty_sub_id T A[σ]Ty[T])) (ty_sub_comp T σ id A)
          ▸[T] t[σ]Tm[T])).
      * apply func_proper. symmetry. apply tm_conv_comp.
      * transitivity (transitivity
          (transitivity (symmetry (ty_sub_id T A[σ]Ty[T])) (ty_sub_comp T σ id A))
          (ty_sub_equiv T (comp_id_r σ) A) ▸[T] t[σ]Tm[T]).
        -- symmetry. apply tm_conv_comp.
        -- apply tm_conv_id.
    + symmetry. apply term_section_pair.
Qed.

End ContextSectionLaws.
