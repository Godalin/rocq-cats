From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Terminal
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Context.Extension
  DTT.Context.Representation
  DTT.Display.Core.

(* Generated storage and inherited choices must select the supplied witnesses. *)
Section StoredChoices.
Context {C : Cat} (T : Fct (C^op) FamCat)
  (HT KT : HasTerminal C) (HC KC : HasContextExtension T).

Definition packed_cwf
  : CwF C
  := MakeCwF C T HT HC.

Example stored_functor
  : (packed_cwf : Fct (C^op) FamCat) = T.
Proof. reflexivity. Qed.

Example stored_terminal
  : hasTerminal packed_cwf = HT.
Proof. reflexivity. Qed.

Example stored_extensions
  : hasContextExtension packed_cwf = HC.
Proof. reflexivity. Qed.

Example other_terminal
  : hasTerminal (MakeCwF C T KT KC) = KT.
Proof. reflexivity. Qed.

Example other_extensions
  : hasContextExtension (MakeCwF C T KT KC) = KC.
Proof. reflexivity. Qed.

End StoredChoices.

(* The underlying functor is primary; instances recover its stored choices. *)
Section PackedClients.
Context {C : Cat} (W : CwF C).

Definition packed_extension {Γ : C} (A : Ty W Γ)
  : C
  := Ext W A.

Definition packed_terminal_arrow (Γ : C)
  : Hom Γ (@Term C (hasTerminal W))
  := ![Γ].

Example packed_pair_rewrite {Γ Δ : C} (A : Ty W Γ)
    (σ : Hom Δ Γ) (t u : Tm W Δ A[σ]Ty[W]) (H : t ≈S u)
  : context_pair W A σ t ≈ context_pair W A σ u.
Proof. rewrite H. reflexivity. Qed.

End PackedClients.

(* Large type/term fibers stay independent of both strict native Hom orders. *)
Section PackedLevels.
Universes o h p l a b c d.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
  (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HT : HasTerminal C) (KT : HasTerminal D)
  (HC : HasContextExtension T) (KC : HasContextExtension U).

Definition packed_high_equality
  : CwF C
  := MakeCwF C T HT HC.

Definition packed_low_equality
  : CwF D
  := MakeCwF D U KT KC.

Definition packed_high_term {Γ : C} (A : Ty T Γ)
  : SetC@{b d}
  := Tm packed_high_equality Γ A.

Definition packed_low_term {Γ : D} (A : Ty U Γ)
  : SetC@{d b}
  := Tm packed_low_equality Γ A.

End PackedLevels.
