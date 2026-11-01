From Cats Require Import Cat.Core Cat.Functor DTT.Display DTT.CwF DTT.Context.Pullback.
From Cats Require Import DTT.Context.Conversion.
From Cats Require Import Instance.Set.Fam.Cat.

(** * Coherent Display Maps from Context Extensions

    Forget terms in the existing family-valued presheaf. The chosen display
    structure must be enabled explicitly; no terminal object is needed. *)

Section ContextDisplay.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Program Definition ContextExtension_HasDisplay : HasDisplay C (FamBaseF ∘F T) :=
  {| Display Γ A := Γ ▹[T] A
   ; display_proj Γ A := context_proj T A
   ; display_conv Γ A B e := e^Ext[T]
   ; display_lift Γ Δ σ A := σ^+[T, A] |}.
Next Obligation. apply context_conv_proj. Defined.
Next Obligation. apply context_conv_id. Qed.
Next Obligation. apply context_conv_comp. Qed.
Next Obligation. apply context_lift_pullback. Defined.
Next Obligation.
  transitivity ((ty_sub_id T A)^Ext[T]).
  - apply context_lift_id.
  - apply context_conv_witness_independent.
Qed.
Next Obligation.
  transitivity ((σ ∘ τ)^+[T, A] ∘ (ty_sub_comp T σ τ A)^Ext[T]).
  - apply context_lift_comp.
  - apply comp_l. apply context_conv_witness_independent.
Qed.
Next Obligation.
  transitivity (σ'^+[T, A] ∘ (ty_sub_equiv T H A)^Ext[T]).
  - apply context_lift_equiv.
  - apply comp_l. apply context_conv_witness_independent.
Qed.
Next Obligation. apply context_lift_conv. Qed.

End ContextDisplay.
