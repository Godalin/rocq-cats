From Cats Require Import Cat.Core Cat.Functor Cat.Natural DTT.CwF.
From Cats Require Import Instance.Set.Core Instance.Set.Hom Instance.Set.Fam
  Instance.Set.FamCat.

(** * Context Extensions Represent Substitutions with a Term *)

Section ContextPairs.
Context {C : Cat} (T : Functor (C^op) FamCat).

Program Definition ty_sub_at_resp {Γ Δ : @Ob C} (A : Ty T Γ)
  : HomSet Δ Γ →r Ty T Δ := {| func σ := A[σ]Ty[T] |}.
Next Obligation. intros σ σ' H. exact (ty_sub_equiv T H A). Defined.

Definition SubstitutionTerms {Γ : @Ob C} (A : Ty T Γ) (Δ : @Ob C)
  : FamS (HomSet Δ Γ) := (Tm T Δ)[ty_sub_at_resp A]S.

Definition ContextPairS {Γ : @Ob C} (A : Ty T Γ) (Δ : @Ob C) : SetC :=
  SigS (HomSet Δ Γ) (SubstitutionTerms A Δ).

Program Definition context_pair_sub_resp {Γ Δ Θ : @Ob C} (A : Ty T Γ)
    (τ : Hom Θ Δ) : ContextPairS A Δ →r ContextPairS A Θ :=
  {| func x := (x.1 ∘ τ; ty_sub_comp T x.1 τ A ▸[T] x.2[τ]Tm[T]) |}.
Next Obligation.
  intros [σ t] [σ' u] [H Ht].
  pose (Hτ := @comp_proper C _ _ _ σ σ' H τ τ (reflexivity τ)).
  exists Hτ.
  change (ty_sub_equiv T Hτ A ▸[T]
    (ty_sub_comp T σ τ A ▸[T] t[τ]Tm[T]) ≈S
    ty_sub_comp T σ' τ A ▸[T] u[τ]Tm[T]).
  transitivity (ty_sub_comp T σ' τ A ▸[T]
    (@func_proper _ _ (ty_sub T τ) _ _ (ty_sub_equiv T H A) ▸[T] t[τ]Tm[T])).
  - transitivity (transitivity (ty_sub_comp T σ τ A) (ty_sub_equiv T Hτ A)
      ▸[T] t[τ]Tm[T]).
    + symmetry. apply tm_conv_comp.
    + apply tm_conv_comp.
  - apply func_proper. transitivity ((ty_sub_equiv T H A ▸[T] t)[τ]Tm[T]).
    + symmetry. apply tm_sub_conv.
    + apply func_proper. exact Ht.
Defined.

End ContextPairs.

Notation "x '[' τ ']Pair[' T ',' A ']'" := (context_pair_sub_resp T A τ x)
  (at level 8, left associativity, format "x [ τ ]Pair[ T ,  A ]") : cat_scope.

Section ContextPairPresheaf.
Context {C : Cat} (T : Functor (C^op) FamCat).

Global Instance context_pair_sub_proper {Γ Δ Θ : @Ob C} (A : Ty T Γ)
  : Proper (HomEq ==> FunEq) (context_pair_sub_resp T A (Δ := Δ) (Θ := Θ)).
Proof.
  intros τ τ' H [σ t].
  pose (Hσ := @comp_proper C _ _ _ σ σ (reflexivity σ) τ τ' H).
  exists Hσ.
  change (ty_sub_equiv T Hσ A ▸[T]
    (ty_sub_comp T σ τ A ▸[T] t[τ]Tm[T]) ≈S
    ty_sub_comp T σ τ' A ▸[T] t[τ']Tm[T]).
  transitivity (ty_sub_comp T σ τ' A ▸[T]
    (ty_sub_equiv T H A[σ]Ty[T] ▸[T] t[τ]Tm[T])).
  - transitivity (transitivity (ty_sub_comp T σ τ A) (ty_sub_equiv T Hσ A)
      ▸[T] t[τ]Tm[T]).
    + symmetry. apply tm_conv_comp.
    + apply tm_conv_comp.
  - apply func_proper. apply tm_sub_equiv.
Defined.

Theorem context_pair_sub_id {Γ Δ : @Ob C} (A : Ty T Γ) (x : ContextPairS T A Δ)
  : x[id]Pair[T, A] ≈S x.
Proof.
  destruct x as [σ t]. exists (comp_id_r σ).
  change (ty_sub_equiv T (comp_id_r σ) A ▸[T]
    (ty_sub_comp T σ id A ▸[T] t[id]Tm[T]) ≈S t).
  transitivity (ty_sub_id T A[σ]Ty[T] ▸[T] t[id]Tm[T]).
  - symmetry. apply tm_conv_comp.
  - apply tm_sub_id.
Defined.

Theorem context_pair_sub_comp {Γ Δ Θ Ξ : @Ob C} (A : Ty T Γ)
    (τ : Hom Θ Δ) (υ : Hom Ξ Θ) (x : ContextPairS T A Δ)
  : x[τ ∘ υ]Pair[T, A] ≈S x[τ]Pair[T, A][υ]Pair[T, A].
Proof.
  destruct x as [σ t]. pose (H := symmetry (comp_assoc σ τ υ)). exists H.
  change (ty_sub_equiv T H A ▸[T]
    (ty_sub_comp T σ (τ ∘ υ) A ▸[T] t[τ ∘ υ]Tm[T]) ≈S
    ty_sub_comp T (σ ∘ τ) υ A ▸[T]
      (ty_sub_comp T σ τ A ▸[T] t[τ]Tm[T])[υ]Tm[T]).
  transitivity (ty_sub_equiv T H A ▸[T]
    (ty_sub_comp T σ (τ ∘ υ) A ▸[T]
      (ty_sub_comp T τ υ A[σ]Ty[T] ▸[T] t[τ]Tm[T][υ]Tm[T]))).
  - apply func_proper. apply func_proper. symmetry. apply tm_sub_comp.
  - transitivity (transitivity (ty_sub_comp T τ υ A[σ]Ty[T])
      (transitivity (ty_sub_comp T σ (τ ∘ υ) A) (ty_sub_equiv T H A))
      ▸[T] t[τ]Tm[T][υ]Tm[T]).
    + transitivity (ty_sub_equiv T H A ▸[T]
        (transitivity (ty_sub_comp T τ υ A[σ]Ty[T])
          (ty_sub_comp T σ (τ ∘ υ) A) ▸[T] t[τ]Tm[T][υ]Tm[T])).
      * apply func_proper. symmetry. apply tm_conv_comp.
      * symmetry. apply tm_conv_comp.
    + transitivity (ty_sub_comp T (σ ∘ τ) υ A ▸[T]
        (@func_proper _ _ (ty_sub T υ) _ _ (ty_sub_comp T σ τ A)
          ▸[T] t[τ]Tm[T][υ]Tm[T])).
      * apply tm_conv_comp.
      * apply func_proper. symmetry. apply tm_sub_conv.
Defined.

Program Definition ContextPairF {Γ : @Ob C} (A : Ty T Γ)
  : Functor (C^op) SetCat :=
  {| F0 := ContextPairS T A
   ; F1 Δ Θ τ := context_pair_sub_resp T A τ |}.
Next Obligation. intros τ τ' H x. exact (context_pair_sub_proper A τ τ' H x). Defined.
Next Obligation. intros x. apply context_pair_sub_id. Defined.
Next Obligation. intros x. apply context_pair_sub_comp. Defined.

End ContextPairPresheaf.

Section ContextRepresentation.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Program Definition context_pair_resp {Γ : @Ob C} (A : Ty T Γ) (Δ : @Ob C)
  : ContextPairS T A Δ →r HomSet Δ (Γ ▹[T] A) :=
  {| func x := ⟨x.1; x.2⟩[T, A] |}.
Next Obligation.
  intros [σ t] [σ' u] [H Ht]. apply (context_pair_equiv T A H). exact Ht.
Defined.

Program Definition context_unpair_resp {Γ : @Ob C} (A : Ty T Γ) (Δ : @Ob C)
  : HomSet Δ (Γ ▹[T] A) →r ContextPairS T A Δ :=
  {| func h := (context_proj T A; context_var T A)[h]Pair[T, A] |}.
Next Obligation.
  intros h h' H. exact (context_pair_sub_proper T A h h' H
    (context_proj T A; context_var T A)).
Defined.

Definition context_extension_iso {Γ : @Ob C} (A : Ty T Γ) (Δ : @Ob C)
  : HomSet Δ (Γ ▹[T] A) ≅[SetCat] ContextPairS T A Δ.
Proof.
  exists (context_unpair_resp A Δ), (context_pair_resp A Δ). split.
  - intros h. symmetry. apply context_pair_η.
  - intros [σ t]. exists (context_pair_β1 T A σ t).
    change (ty_sub_equiv T (context_pair_β1 T A σ t) A ▸[T]
      (ty_sub_comp T (context_proj T A) ⟨σ; t⟩[T, A] A ▸[T]
        (context_var T A)[⟨σ; t⟩[T, A]]Tm[T]) ≈S t).
    transitivity (ty_sub_comm T A (context_proj T A) ⟨σ; t⟩[T, A]
      (context_pair_β1 T A σ t) ▸[T] (context_var T A)[⟨σ; t⟩[T, A]]Tm[T]).
    + symmetry. apply tm_conv_comp.
    + apply context_pair_β2.
Defined.

(** Pairing reflects equality of terms over the same base substitution. *)
Theorem context_pair_inj {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t u : Tm T Δ A[σ]Ty[T])
  : ⟨σ; t⟩[T, A] ≈ ⟨σ; u⟩[T, A] → t ≈S u.
Proof.
  intros H. pose (Hβ := snd (context_extension_iso A Δ).2.2).
  assert (Hd : ((σ; t) : ContextPairS T A Δ) ≈S (σ; u)).
  { transitivity (context_unpair_resp A Δ ⟨σ; t⟩[T, A]).
    - symmetry. exact (Hβ (σ; t)).
    - transitivity (context_unpair_resp A Δ ⟨σ; u⟩[T, A]).
      + apply func_proper. exact H.
      + exact (Hβ (σ; u)). }
  destruct Hd as [Hσ Ht].
  transitivity (ty_sub_equiv T Hσ A ▸[T] t).
  - symmetry. apply tm_conv_id.
  - exact Ht.
Qed.

(** Eta with an arbitrary equivalent base map, retaining its witness. *)
Theorem context_pair_η_base {Γ Δ : @Ob C} (A : Ty T Γ)
    (h : Hom Δ (Γ ▹[T] A)) (σ : Hom Δ Γ) (H : context_proj T A ∘ h ≈ σ)
  : h ≈ ⟨σ; ty_sub_comm T A (context_proj T A) h H
      ▸[T] (context_var T A)[h]Tm[T]⟩[T, A].
Proof. apply context_pair_unique. exists H. reflexivity. Qed.

(** The representing map evaluates the generic pair along a substitution. *)
Program Definition context_extensionN {Γ : @Ob C} (A : Ty T Γ)
  : Hom(-, Γ ▹[T] A) => ContextPairF T A :=
  {| nt Δ := context_unpair_resp A Δ |}.
Next Obligation.
  intros h. change ((context_proj T A; context_var T A)[h ∘ f]Pair[T, A]
    ≈S (context_proj T A; context_var T A)[h]Pair[T, A][f]Pair[T, A]).
  apply context_pair_sub_comp.
Defined.

Definition context_extension_nat_iso {Γ : @Ob C} (A : Ty T Γ)
  : Hom(-, Γ ▹[T] A) ≅N ContextPairF T A.
Proof.
  exists (context_extensionN A). intros Δ.
  exists (context_pair_resp A Δ). exact (context_extension_iso A Δ).2.2.
Defined.

Definition context_pairN {Γ : @Ob C} (A : Ty T Γ)
  : ContextPairF T A => Hom(-, Γ ▹[T] A) :=
  (context_extensionN A) ^-1N (context_extension_nat_iso A).2.

Theorem context_pair_comp {Γ Δ Θ : @Ob C} (A : Ty T Γ)
    (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T]) (τ : Hom Θ Δ)
  : ⟨σ; t⟩[T, A] ∘ τ ≈
      ⟨σ ∘ τ; ty_sub_comp T σ τ A ▸[T] t[τ]Tm[T]⟩[T, A].
Proof. symmetry. exact (nt_naturality (context_pairN A) τ (σ; t)). Qed.

End ContextRepresentation.
