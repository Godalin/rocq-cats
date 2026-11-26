From Cats Require Import
  Cat.Profunctor.StrongCompose
  Cat.Profunctor.HomStrength
  Cat.Profunctor.LeftUnit
  Instance.Set.Core
  Instance.Set.Monoid
  Instance.Bool.Group.

Local Open Scope monoidal_scope.
Local Open Scope prof_scope.
Local Open Scope ob_scope.

(** * Selected components of strong profunctors

    The generated native functor view and strength projection must read
    the supplied components even when a second strength is available. *)

(** Keep this test helper transparent: [inherited_component] reduces the
    selected instance to the component of a supplied bundle. *)

Definition inherited_strength {C : Cat} {MC : HasMonoidal C}
    (P : StrongProf MC)
  : HasProfStrength MC P.
Proof. typeclasses eauto. Defined.

Section Choices.
Context {C : Cat} (MC : HasMonoidal C)
  (P : Fct ((C^op) ×C C) SetCat)
  (first second : HasProfStrength MC P).

Definition first_prof
  : StrongProf MC
  := MakeStrongProf P first.
Definition second_prof
  : StrongProf MC
  := MakeStrongProf P second.

Example first_functor
  : StrongProfToFct first_prof = P
  := eq_refl.
Example first_strength
  : hasProfStrength first_prof = first
  := eq_refl.
Example second_strength
  : hasProfStrength second_prof = second
  := eq_refl.
Fail Check (eq_refl : hasProfStrength first_prof = second).

Example inherited_component
  : inherited_strength first_prof = first
  := eq_refl.

Fail Definition unchosen_bundle
  : StrongProf MC
  := ltac:(typeclasses eauto).
End Choices.

(** * Rewriting through the lifted composition operation

    This checks the registered Proper instance by an actual rewrite on
    subset morphisms, without comparing their preservation witnesses. *)

Section Rewriting.
Context {C : Cat} (MC : HasMonoidal C)
  (Q Q' P P' : StrongProf MC)
  `{HC : !HasProfComp C C C Q P}
  `{HC' : !HasProfComp C C C Q' P'}.
Context (β β' : StrongProfHomS MC Q Q')
  (α α' : StrongProfHomS MC P P')
  (Eβ : β ≈S β') (Eα : α ≈S α').

Example rewrite_composite
  : @carrier_equiv
      (StrongProfHomS MC
        (@StrongProfComp C MC Q P HC) (@StrongProfComp C MC Q' P' HC'))
      (@StrongProfCompMap C MC Q Q' P P' HC HC' β α)
      (@StrongProfCompMap C MC Q Q' P P' HC HC' β' α').
Proof. rewrite Eβ, Eα. reflexivity. Qed.
End Rewriting.

(** * Actual special coends and transparent strength

    Hom-after-Hom uses the existing special co-Yoneda choice, not a
    generated full-SetCat self-indexed coend. *)

Module HomModel.
Definition C
  := SetCat@{Set Set _ _ _ _ _}.
Definition MC
  : HasMonoidal C
  := SetCartMonoidal.
Definition H
  : Fct ((C^op) ×C C) (SetCat@{Set Set _ _ _ _ _})
  := HomProf C.
Definition S
  : HasProfStrength MC H
  := HomProfStrength MC.
Definition A
  : StrongProf MC
  := MakeStrongProf H S.
Definition HC
  : HasProfComp C C C H H
  := ProfLeftUnitComp H.
Definition CP
  := @StrongProfComp C MC A A HC.
Definition a
  := strong_prof_id MC A.
Definition mapped
  := @StrongProfCompMap C MC A A A A HC HC a a.
Definition input
  : CP (BoolS,BoolS)
  := Lift (id_resp (X := BoolS)).

Example composite_identity_computes (b : bool)
  : lower (mapped.1 (BoolS,BoolS) input) b = b.
Proof. destruct b; vm_compute; reflexivity. Qed.

Example context_computes (z b : bool)
  : lower (@prof_strength C MC CP (hasProfStrength CP)
      BoolS BoolS BoolS input) (z,b) = (z,b).
Proof. destruct z,b; vm_compute; reflexivity. Qed.

Example full_coend_inverse
  : (@prof_left_unit_in C C H BoolS BoolS
        (@hasProfCompCoend C C C H H HC BoolS BoolS) ∘r
      @prof_left_unit_out C C H BoolS BoolS
        (@hasProfCompCoend C C C H H HC BoolS BoolS)) ≈f id_resp.
Proof. apply prof_left_unit_in_out. Qed.
End HomModel.
