From Cats Require Import Cat.Core Cat.Functor Cat.Pullback Cat.Section DTT.Display.
From Cats Require Import Instance.Set.Core.
From Cats Require Import Instance.Set.Fam.Core Instance.Set.Fam.Cat.

(** * Terms as Sections of Coherent Display Maps

    Conversion acts over a fixed context. Substitution is the unique section
    induced by the chosen display pullback. Its coherence follows from the
    display squares, without a prior family-valued presheaf or CwF. *)

Section DisplayTerms.
Context {C : Cat} (P : Functor (C^op) SetCat) `{HD : !HasDisplay C P}.

Definition display_term_conv_resp@{s +} {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
  : SectionOfS@{s _ _ _ _} (display_proj P A) →r
    SectionOfS@{s _ _ _ _} (display_proj P B) :=
  section_of_map_resp (e^D[P]) (display_conv_proj e).

Program Definition DisplayTerms@{s +} (Γ : @Ob C) : FamS@{_ _ _ s _} (P Γ) :=
  {| fam A := Sec(display_proj P A)
   ; transpS A B e := display_term_conv_resp e |}.
Next Obligation.
  change (p^D[P] ∘ v.1 ≈ v.1).
  rewrite display_conv_id. apply comp_id_l.
Qed.
Next Obligation.
  change (r^D[P] ∘ v.1 ≈ q^D[P] ∘ (p^D[P] ∘ v.1)).
  rewrite (display_conv_comp p q r). apply comp_assoc.
Qed.

Program Definition DisplayTyTm (Γ : @Ob C) : FamC :=
  {| famC_base := P Γ; famC_fam := DisplayTerms Γ |}.

Definition display_term_sub_resp {Γ Δ : @Ob C} (σ : Hom Δ Γ) {A : P Γ}
  : DisplayTerms Γ A →r DisplayTerms Δ A[σ]TyF[P] :=
  section_of_pullback_resp (display_lift_universal σ A).

End DisplayTerms.

Notation "e '▸D[' P ']' s" := (display_term_conv_resp P e s)
  (at level 40, left associativity, format "e  ▸D[ P ]  s") : cat_scope.
Notation "s '[' σ ']TmD[' P ']'" := (display_term_sub_resp P σ s)
  (at level 8, left associativity, format "s [ σ ]TmD[ P ]") : cat_scope.

Section DisplayTermLaws.
Context {C : Cat} (P : Functor (C^op) SetCat) `{HD : !HasDisplay C P}.

Definition display_term_sub_β {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
    (s : DisplayTerms P Γ A)
  : σ^D[P, A] ∘ s[σ]TmD[P].1 ≈ s.1 ∘ σ :=
  section_of_pullback_β (display_lift_universal σ A) s.

Theorem display_term_sub_conv {Γ Δ : @Ob C} (σ : Hom Δ Γ)
    {A B : P Γ} (e : A ≈S B) (s : DisplayTerms P Γ A)
  : (e ▸D[P] s)[σ]TmD[P] ≈S e[σ]EqF[P] ▸D[P] s[σ]TmD[P].
Proof.
  symmetry. apply section_of_pullback_unique.
  change (σ^D[P, B] ∘ (e[σ]EqF[P]^D[P] ∘ s[σ]TmD[P].1)
    ≈ (e^D[P] ∘ s.1) ∘ σ).
  rewrite <- comp_assoc, display_lift_conv, comp_assoc, display_term_sub_β.
  apply symmetry, comp_assoc.
Qed.

Theorem display_term_sub_id {Γ : @Ob C} (A : P Γ) (s : DisplayTerms P Γ A)
  : type_sub_id P A ▸D[P] s[id]TmD[P] ≈S s.
Proof.
  change ((type_sub_id P A)^D[P] ∘ s[id]TmD[P].1 ≈ s.1).
  rewrite <- display_lift_id, display_term_sub_β. apply comp_id_r.
Qed.

Theorem display_term_sub_comp {Γ Δ Θ : @Ob C}
    (σ : Hom Δ Γ) (τ : Hom Θ Δ) (A : P Γ) (s : DisplayTerms P Γ A)
  : type_sub_comp P σ τ A ▸D[P] s[σ]TmD[P][τ]TmD[P] ≈S s[σ ∘ τ]TmD[P].
Proof.
  apply section_of_pullback_unique.
  change ((σ ∘ τ)^D[P, A] ∘ ((type_sub_comp P σ τ A)^D[P] ∘
    s[σ]TmD[P][τ]TmD[P].1) ≈ s.1 ∘ (σ ∘ τ)).
  rewrite <- comp_assoc, <- display_lift_comp, comp_assoc, display_term_sub_β,
    <- comp_assoc, display_term_sub_β. apply comp_assoc.
Qed.

Theorem display_term_sub_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ}
    (H : σ ≈ σ') (A : P Γ) (s : DisplayTerms P Γ A)
  : type_sub_equiv P H A ▸D[P] s[σ]TmD[P] ≈S s[σ']TmD[P].
Proof.
  apply section_of_pullback_unique.
  change (σ'^D[P, A] ∘ ((type_sub_equiv P H A)^D[P] ∘ s[σ]TmD[P].1)
    ≈ s.1 ∘ σ').
  rewrite <- comp_assoc, <- display_lift_equiv, display_term_sub_β.
  apply comp_l. exact H.
Qed.

Program Definition display_sub_fam {Γ Δ : @Ob C} (σ : Hom Δ Γ)
  : FamF (DisplayTyTm P Γ) (DisplayTyTm P Δ) :=
  {| famF_base := type_sub P σ
   ; famF_fam A := display_term_sub_resp P σ (A := A) |}.
Next Obligation. apply display_term_sub_conv. Qed.

Program Definition DisplayTyTmF : Functor (C^op) FamCat :=
  {| F0 := DisplayTyTm P
   ; F1 Γ Δ σ := display_sub_fam σ |}.
Next Obligation.
  intros σ σ' H. exists (λ A, type_sub_equiv P H A).
  intros A s. apply display_term_sub_equiv.
Defined.
Next Obligation.
  exists (λ A, type_sub_id P A). intros A s. apply display_term_sub_id.
Defined.
Next Obligation.
  apply symmetry. exists (λ A, type_sub_comp P g f A).
  intros A s. apply display_term_sub_comp.
Defined.

End DisplayTermLaws.
