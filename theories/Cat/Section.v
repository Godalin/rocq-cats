From Cats Require Import Cat.Core Cat.Pullback.

(** * Sections of a Morphism

    Right-inverse witnesses are retained; equality compares the maps. *)

Definition SectionOfEq {C : Cat} {X Y : @Ob C} (p : Hom X Y)
    (s t : ∃ s : Hom Y X, p ∘ s ≈ id) := s.1 ≈ t.1.

Global Instance SectionOfEq_Equivalence@{s l +}
    {C : Cat@{_ _ _ l l}} {X Y : @Ob C} (p : Hom X Y)
  : Equivalence@{s _} (SectionOfEq p).
Proof.
  split; unfold SectionOfEq.
  - intros s. reflexivity.
  - intros s t H. symmetry. exact H.
  - intros s t u H K. transitivity t.1; assumption.
Defined.

(** The section carrier contains a map and its right-inverse witness. Its
    size [s] is independent of the category-law bound [l]. *)
Definition SectionOfS@{s l +} {C : Cat@{_ _ _ l l}}
    {X Y : @Ob C} (p : Hom X Y) : SetC@{s _} :=
  {| carrier := ∃ s : Hom Y X, p ∘ s ≈ id
   ; carrier_equiv := SectionOfEq p
   ; carrier_setoid := SectionOfEq_Equivalence p |}.

Notation "'Sec(' p ')'" := (SectionOfS p) (format "Sec( p )") : cat_scope.

(** ** Maps over a Fixed Base *)

Program Definition section_of_map_resp@{s l +} {C : Cat@{_ _ _ l l}} {E F Γ : @Ob C}
    {p : Hom E Γ} {q : Hom F Γ} (f : Hom E F) (H : q ∘ f ≈ p)
  : SectionOfS@{s l _ _ _} p →r SectionOfS@{s l _ _ _} q :=
  {| func s := (f ∘ s.1; _) |}.
Next Obligation. rewrite <- comp_assoc, H. exact s.2. Defined.
Next Obligation. intros s t Hst. cbn. apply comp_l. exact Hst. Defined.

Notation "f '▷Sec[' H ']' s" := (section_of_map_resp f H s)
  (at level 40, left associativity, format "f  ▷Sec[ H ]  s") : cat_scope.

Theorem section_of_map_equiv {C : Cat} {E F Γ : @Ob C}
    {p : Hom E Γ} {q : Hom F Γ} {f g : Hom E F}
    (H : q ∘ f ≈ p) (K : q ∘ g ≈ p) {s t : Sec(p)}
    (Hfg : f ≈ g) (Hst : s ≈S t)
  : f ▷Sec[H] s ≈S g ▷Sec[K] t.
Proof. exact (comp_proper f g Hfg s.1 t.1 Hst). Qed.

Theorem section_of_map_id {C : Cat} {E Γ : @Ob C} {p : Hom E Γ}
    (H : p ∘ id ≈ p) (s : Sec(p)) : id ▷Sec[H] s ≈S s.
Proof. apply comp_id_l. Qed.

Theorem section_of_map_comp {C : Cat} {E F G Γ : @Ob C}
    {p : Hom E Γ} {q : Hom F Γ} {r : Hom G Γ}
    (f : Hom E F) (g : Hom F G)
    (Hf : q ∘ f ≈ p) (Hg : r ∘ g ≈ q) (Hgf : r ∘ (g ∘ f) ≈ p)
    (s : Sec(p))
  : (g ∘ f) ▷Sec[Hgf] s ≈S g ▷Sec[Hg] (f ▷Sec[Hf] s).
Proof. apply comp_assoc. Qed.

(** ** Pulling Back Sections

    The given universal property chooses the mediator. No chosen structure
    for other pullback squares is required. *)

Section PullbackSections.
Context {C : Cat} {Γ Δ E D : @Ob C}
    {σ : Hom Δ Γ} {p : Hom E Γ} {q : Hom D Δ} {l : Hom D E}
    (HP : is_pullback σ p D q l).

Definition section_of_pullback_cone (s : Sec(p)) : σ ∘ id ≈ p ∘ (s.1 ∘ σ).
Proof. rewrite <- comp_assoc, s.2, comp_id_l. apply comp_id_r. Defined.

Program Definition section_of_pullback@{s +} (t : SectionOfS@{s _ _ _ _} p)
  : SectionOfS@{s _ _ _ _} q :=
  ((snd HP Δ id (t.1 ∘ σ) (section_of_pullback_cone t)).1; _).
Next Obligation.
  exact (fst (@this _ _ _ _ _
    (snd HP Δ id (t.1 ∘ σ) (section_of_pullback_cone t)).2)).
Defined.

Definition section_of_pullback_β (s : Sec(p))
  : l ∘ (section_of_pullback s).1 ≈ s.1 ∘ σ :=
  snd (@this _ _ _ _ _
    (snd HP Δ id (s.1 ∘ σ) (section_of_pullback_cone s)).2).

Program Definition section_of_pullback_resp@{s +}
  : SectionOfS@{s _ _ _ _} p →r SectionOfS@{s _ _ _ _} q :=
  {| func := section_of_pullback |}.
Next Obligation.
  intros s t Hst. apply (pullback_hom_ext HP).
  - transitivity (@id Δ); [exact (section_of_pullback s).2 |
      symmetry; exact (section_of_pullback t).2].
  - rewrite !section_of_pullback_β. apply comp_r. exact Hst.
Defined.

End PullbackSections.

Notation "s '[' HP ']Sec'" := (section_of_pullback_resp HP s)
  (at level 8, left associativity, format "s [ HP ]Sec") : cat_scope.

Section PullbackSectionLaws.
Context {C : Cat} {Γ Δ E D : @Ob C}
    {σ : Hom Δ Γ} {p : Hom E Γ} {q : Hom D Δ} {l : Hom D E}
    (HP : is_pullback σ p D q l).

Theorem section_of_pullback_unique (s : Sec(p)) (t : Sec(q))
    (H : l ∘ t.1 ≈ s.1 ∘ σ) : t ≈S s[HP]Sec.
Proof.
  apply (pullback_hom_ext HP).
  - transitivity (@id Δ); [exact t.2 | symmetry; exact s[HP]Sec.2].
  - transitivity (s.1 ∘ σ); [exact H | symmetry; apply section_of_pullback_β].
Qed.

End PullbackSectionLaws.
