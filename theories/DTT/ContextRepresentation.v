From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Terminal.
From Cats Require Import DTT.CwF DTT.ContextExtension.
From Cats Require Import Instance.Set.Core Instance.Set.Hom Instance.Set.Fam
  Instance.Set.FamCat.

(** * Recovering Context Extensions from Representations

    The family-valued presheaf already supplies designated type/term equality
    and coherent substitution. A chosen representation supplies the extension. *)

Section ContextRepresentation.
Context {C : Cat} (T : Functor (C^op) FamCat).

Theorem context_pair_data_iff {Γ E Δ : @Ob C} (A : Ty T Γ) (p : Hom E Γ)
    (q : Tm T E A[p]Ty[T]) (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
    (h : Hom Δ E)
  : (p; q)[h]Pair[T, A] ≈S ((σ; t) : ContextPairS T A Δ)
    ↔ is_context_pair T A p q σ t h.
Proof.
  split; intros [H Ht]; exists H.
  - transitivity (ty_sub_equiv T H A ▸[T]
      (ty_sub_comp T p h A ▸[T] q[h]Tm[T])).
    + apply tm_conv_comp.
    + exact Ht.
  - change (ty_sub_equiv T H A ▸[T]
      (ty_sub_comp T p h A ▸[T] q[h]Tm[T]) ≈S t).
    transitivity (ty_sub_comm T A p h H ▸[T] q[h]Tm[T]).
    + symmetry. apply tm_conv_comp.
    + exact Ht.
Defined.

Definition context_representation_generic {Γ : @Ob C} (A : Ty T Γ) {E : @Ob C}
    (R : Hom(-, E) ≅N ContextPairF T A) : ContextPairS T A E := R.1 E id.

(** Naturality determines every component from the generic pair. *)
Theorem context_representation_at {Γ : @Ob C} (A : Ty T Γ) {E : @Ob C}
    (R : Hom(-, E) ≅N ContextPairF T A) {Δ : @Ob C} (h : Hom Δ E)
  : R.1 Δ h ≈S (context_representation_generic A R)[h]Pair[T, A].
Proof.
  transitivity (R.1 Δ (id ∘ h)).
  - apply func_proper. symmetry. apply comp_id_l.
  - exact (nt_naturality R.1 h id).
Defined.

Definition context_extension_of_representation {Γ : @Ob C} (A : Ty T Γ) {E : @Ob C}
    (R : Hom(-, E) ≅N ContextPairF T A)
  : is_context_extension T A E (context_representation_generic A R).1
      (context_representation_generic A R).2.
Proof.
  intros Δ σ t. pose (h := (R.2 Δ).1 (σ; t)).
  exists h. refine {| this := _; that := _ |}.
  - apply (fst (context_pair_data_iff A _ _ σ t h)).
    transitivity (R.1 Δ h).
    + symmetry. apply context_representation_at.
    + exact (snd (R.2 Δ).2 (σ; t)).
  - intros k Hk.
    transitivity ((R.2 Δ).1 (R.1 Δ k)).
    + symmetry. exact (fst (R.2 Δ).2 k).
    + apply func_proper.
      transitivity (context_representation_generic A R)[k]Pair[T, A].
      * apply context_representation_at.
      * exact (snd (context_pair_data_iff A _ _ σ t k) Hk).
Defined.

Class HasContextRepresentation :=
  { ContextRep {Γ : @Ob C} (A : Ty T Γ) : @Ob C
  ; context_representation {Γ : @Ob C} (A : Ty T Γ)
    : Hom(-, ContextRep A) ≅N ContextPairF T A
  }.

(** Both conversions are explicit choices, never selected by import. *)
Program Definition ContextRepresentation_HasContextExtension
    `{HR : !HasContextRepresentation} : HasContextExtension T :=
  {| Ext Γ := ContextRep
   ; context_proj Γ A := (context_representation_generic A (context_representation A)).1
   ; context_var Γ A := (context_representation_generic A (context_representation A)).2
   ; context_extension_universal Γ A :=
       context_extension_of_representation A (context_representation A) |}.

Program Definition ContextExtension_HasContextRepresentation
    `{HC : !HasContextExtension T} : HasContextRepresentation :=
  {| ContextRep Γ := Ext T
   ; context_representation Γ := context_extension_nat_iso T |}.

Theorem context_extension_iff_representation
  : HasContextExtension T ↔ HasContextRepresentation.
Proof.
  split.
  - intros HC. exact (@ContextExtension_HasContextRepresentation HC).
  - intros HR. exact (@ContextRepresentation_HasContextExtension HR).
Defined.

Program Definition RepresentedCwF `{HT : !HasTerminal C} `{HR : !HasContextRepresentation}
  : CwF C :=
  {| hasTerminal := HT
   ; TyTmF := T
   ; hasContextExtension := ContextRepresentation_HasContextExtension |}.

Section ExtensionRoundTrip.
Context `{HC : !HasContextExtension T}.
Let HR := ContextExtension_HasContextRepresentation.
Let HC' := @ContextRepresentation_HasContextExtension HR.

Theorem context_representation_proj_round_trip {Γ : @Ob C} (A : Ty T Γ)
  : @context_proj C T HC' Γ A ≈ @context_proj C T HC Γ A.
Proof. cbn. apply comp_id_r. Defined.

Theorem context_representation_var_round_trip {Γ : @Ob C} (A : Ty T Γ)
  : ty_sub_equiv T (context_representation_proj_round_trip A) A
      ▸[T] (@context_var C T HC' Γ A) ≈S @context_var C T HC Γ A.
Proof.
  transitivity (ty_sub_id T A[@context_proj C T HC Γ A]Ty[T]
    ▸[T] (@context_var C T HC Γ A)[id]Tm[T]).
  - symmetry. apply tm_conv_comp.
  - apply tm_sub_id.
Defined.

Theorem context_representation_pair_round_trip {Γ Δ : @Ob C} (A : Ty T Γ)
    (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
  : @context_pair C T HC' Γ Δ A σ t ≈ @context_pair C T HC Γ Δ A σ t.
Proof. reflexivity. Defined.

End ExtensionRoundTrip.

Theorem context_representation_round_trip `{HR : !HasContextRepresentation}
    {Γ : @Ob C} (A : Ty T Γ)
  : @context_extensionN C T ContextRepresentation_HasContextExtension Γ A
      ≈N (context_representation A).1.
Proof. intros Δ h. symmetry. apply context_representation_at. Defined.

End ContextRepresentation.
