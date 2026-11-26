From Cats Require Import
  Instance.Set.Vertex.Functor
  Cat.Preorder
  Cat.Diagram.Core.

(** Different Type-valued equality witnesses can have the same endpoints.
    They must not be conflated by inference on the underlying functor. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := unit
  ; carrier_equiv _ _ := bool
  |}.
Next Obligation. split; red; intros; exact false. Defined.

Definition WitnessAction
  : Fct (EqGpd WitnessS) (CodiscreteCat unit)
  := ConstF (EqGpd WitnessS) (C := CodiscreteCat unit) tt.

Program Definition FalseWitness
  : IsVtxFct WitnessAction WitnessAction IdF
  :=
  {|vertex_fct_ob_proper _ _ _ := false
  ; vertex_fct_transport := _
  |}.
Next Obligation. exact tt. Qed.

Program Definition TrueWitness
  : IsVtxFct WitnessAction WitnessAction IdF
  :=
  {|vertex_fct_ob_proper _ _ _ := true
  ; vertex_fct_transport := _
  |}.
Next Obligation. exact tt. Qed.

Definition FalsePackage
  : WitnessAction →ᵥ WitnessAction
  := MakeVtxFct IdF FalseWitness.

Definition TruePackage
  : WitnessAction →ᵥ WitnessAction
  := MakeVtxFct IdF TrueWitness.

Example same_underlying_functor
  : VtxFctToFct FalsePackage = VtxFctToFct TruePackage
  := eq_refl.

Example native_parent_path_agrees
  : (@VtxFctToFctCarrier _ _ _ _ WitnessAction WitnessAction FalsePackage
      : Fct (VtxCat WitnessAction) (VtxCat WitnessAction)) =
      VtxFctToFct FalsePackage
  := eq_refl.

Example stored_mixin_kept
  : isVtxFct FalsePackage = FalseWitness
  := eq_refl.

Example identity_functor_view
  : VtxFctToFct (VtxIdF WitnessAction) = IdF
  := eq_refl.

Example composition_functor_view
  : VtxFctToFct (FalsePackage ∘Fᵥ TruePackage) =
      VtxFctToFct FalsePackage ∘F VtxFctToFct TruePackage
  := eq_refl.

Example composition_false_witness
  : @func_proper _ _
      (vertex_fct_ob_resp (FalsePackage ∘Fᵥ TruePackage)) tt tt true = false
  := eq_refl.

Example composition_true_witness
  : @func_proper _ _
      (vertex_fct_ob_resp (TruePackage ∘Fᵥ FalsePackage)) tt tt false = true
  := eq_refl.

Fail Check Cats.Instance.Set.Vertex.Functor.vertex_fct.
Fail Check Cats.Instance.Set.Vertex.Functor.Build_VtxFct.

Section CompetingWitness.
Local Existing Instance TrueWitness.

Example false_choice_still_stored
  : @func_proper _ _ (vertex_fct_ob_resp FalsePackage) tt tt true = false
  := eq_refl.

Example true_choice_still_stored
  : @func_proper _ _ (vertex_fct_ob_resp TruePackage) tt tt false = true
  := eq_refl.

Fail Definition choices_not_identified
  : @func_proper _ _ (vertex_fct_ob_resp FalsePackage) tt tt true =
      @func_proper _ _ (vertex_fct_ob_resp TruePackage) tt tt true
  := eq_refl.

End CompetingWitness.

(** Actual rewriting uses the respectful view of the same native object
    map. The explicit view fixes the selected transport witness. *)

Section Rewriting.
Context {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    (F : T →ᵥ U) (x y : X) (e : x ≈S y).

Example object_map_rewrites
  : (F x : Y) ≈S F y.
Proof.
  change (vertex_fct_ob_resp F x ≈S vertex_fct_ob_resp F y).
  rewrite e. reflexivity.
Qed.

Example stored_instance_available
  : Proper (carrier_equiv X ==> carrier_equiv Y) F
  := VtxFct_Proper F.

End Rewriting.

(** Native label and ambient hom-equality sizes remain independent. *)

Section StrictSizes.
Universes e h o l.
Constraint e < h, h < o, o < l.
Context (X : SetC@{o e}) (Y : SetC@{e o})
    (C : Cat@{o h e l l}) (D : Cat@{e h o l l})
    (T : Fct (EqGpd X) C) (U : Fct (EqGpd Y) D).

Definition forward_maps
  : SetC@{l o}
  := VtxFctS T U.

Definition reverse_maps
  : SetC@{l h}
  := VtxFctS U T.

End StrictSizes.
