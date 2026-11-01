From Cats Require Import Cat.Core Cat.Functor Cat.Terminal DTT.CwF.
From Cats Require Import Instance.Set.Core Instance.Set.Terminal.
From Cats Require Import Instance.Set.Fam.Core Instance.Set.Fam.Cat Instance.Set.Fam.Fixed.
From Cats Require Import Instance.Set.Fam.Section Instance.Set.Fam.SectionMap.

(** * A CwF from Type Codes and Their Decoding Family

    Types are respectful code-valued functions. Terms are coherent sections
    of the decoded family; type equality and term equality are pointwise.
    No closure under type formers is required of the chosen codes. *)

Section CodeFamilies.
Context {Code : SetC} (El : FamS Code).

Program Definition CodeTerms (Γ : SetC) : FamS (Γ →S Code) :=
  {| fam A := SectionS El[A]S
   ; transpS A B H := section_fam_map_resp El⟦H⟧Fam |}.
Next Obligation. intros γ. cbn. apply transpS_id. Defined.
Next Obligation. intros γ. cbn. apply transpS_comp. Defined.

Definition CodeFamily (Γ : SetC) : FamC :=
  {| famC_base := Γ →S Code; famC_fam := CodeTerms Γ |}.

Program Definition code_sub {Δ Γ : SetC} (σ : Δ →r Γ)
  : FamF (CodeFamily Γ) (CodeFamily Δ) :=
  {| famF_base := {| func A := A ∘r σ |}
   ; famF_fam A := section_fam_map_resp El⟨A, σ⟩Fam
       ∘r section_reindex_resp El[A]S σ |}.
Next Obligation. intros A B H δ. exact (H (σ δ)). Defined.
Next Obligation. intros δ. cbn. apply transpS_witness_independent. Defined.

Program Definition CodeTyTmF : Functor (SetCat^op) FamCat :=
  {| F0 := CodeFamily
   ; F1 Γ Δ σ := code_sub σ |}.
Next Obligation.
  intros σ τ H. exists (λ A δ, @func_proper _ _ A _ _ (H δ)).
  intros A s δ. cbn. exact (section_proper s (H δ)).
Defined.
Next Obligation.
  exists (λ (A : X →r Code) δ, reflS (x := A δ)).
  intros A s δ. cbn. apply transpS_id.
Defined.
Next Obligation.
  exists (λ (A : X →r Code) δ, reflS (x := A (g (f δ)))).
  intros A s δ. cbn. apply transpS_id.
Defined.

(** Convert a section along the inverse decoding-composition comparison,
    then use the existing total-space pairing. The resulting map computes
    to [(σ δ; t δ)]. *)
Definition code_pair_resp {Δ Γ : SetC} (A : Γ →r Code) (σ : Δ →r Γ)
    (t : SectionS El[A ∘r σ]S) : Δ →r SigS Γ El[A]S :=
  section_pair_resp El[A]S σ ((fam_map_reindex_comp_iso A σ El).1 ▷Fam t).

Program Definition CodeExtensions : HasContextExtension CodeTyTmF :=
  {| Ext Γ A := SigS Γ El[A]S
   ; context_proj Γ A := sig_base_resp El[A]S
   ; context_var Γ A :=
       El⟨A, sig_base_resp El[A]S⟩Fam ▷Fam section_var El[A]S |}.
Next Obligation.
  intros Δ σ t. exists (code_pair_resp A σ t). split.
  - exists (λ δ, reflS (x := σ δ)). intros δ. cbn. apply transpS_id.
  - intros h [H Ht] δ. exists (H δ).
    transitivity (transpS El
      (ty_sub_comm CodeTyTmF A (sig_base_resp El[A]S) h H δ) (h δ).2).
    + exact (transpS_witness_independent El _ _ (h δ).2).
    + exact (Ht δ).
Defined.

(** Enable a chosen model explicitly to obtain its terminal context and
    context extensions through the abstract CwF interface. *)
Program Definition SetCwF : CwF SetCat :=
  {| hasTerminal := SetCat_HasTerminal
   ; TyTmF := CodeTyTmF
   ; hasContextExtension := CodeExtensions |}.

End CodeFamilies.
