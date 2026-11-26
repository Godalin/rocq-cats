From Cats Require Import
  Cat.Gluing.Change
  Cat.Pullback
  Cat.Morphism
  Cat.Diagram.Arrow
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Bool.Group.
From CatsTests.gluing Require Import
  Gluing
  GluingFibration.

(** * Model Change and Cartesian Gluing Images

    Strict category profiles check independent base/target levels through
    consecutive changes. Concrete arrow diagrams distinguish an incoming
    isomorphism from an outgoing monomorphism and test failure without the
    needed incoming inverse. No model choice is enabled globally. *)

(** ** Independent Category Levels

    Fix six separate base/target categories and compatible changes.
    The candidate preservation theorem uses only the supplied image square. *)

Section IndependentChange.
Universes
  o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5.
Constraint h0 < e0, e0 < o0, o0 < l0.
Constraint e1 < h1, h1 < o1, o1 < l1.
Constraint h2 < e2, e2 < o2, o2 < l2.
Constraint e3 < h3, h3 < o3, o3 < l3.
Constraint h4 < e4, e4 < o4, o4 < l4.
Constraint e5 < h5, h5 < o5, o5 < l5.
Constraint l0 < o1, l1 < o2, l2 < o3, l3 < o4, l4 < o5.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {C'' : Cat@{o4 h4 e4 l4 l4}}.
Context {D'' : Cat@{o5 h5 e5 l5 l5}}.
Context {F : Fct C D} {F' : Fct C' D'} {F'' : Fct C'' D''}.
Context (H : Fct C C') (K : Fct D D').
Context (H' : Fct C' C'') (K' : Fct D' D'').
Context (α : (K ∘F F) ⇒ (F' ∘F H))
    (β : (K' ∘F F') ⇒ (F'' ∘F H')).

(** The actual change functor accepts these strict boundaries. *)

Definition independent_gluing_change
  : Fct (Gluing F) (Gluing F')
  := GluingChangeF H K α.

(** Both projections retain their separate ambient categories. *)

Definition independent_gluing_projection
  : (GluingRightF F' ∘F GluingChangeF H K α) ≅N (H ∘F GluingRightF F)
  := gluing_change_base_iso H K α.

(** Composite compatibility uses all six category boundaries. *)

Definition independent_gluing_composite
  : (GluingChangeF H' K' β ∘F GluingChangeF H K α) ≅N
      GluingChangeF (H' ∘F H) (K' ∘F K)
        (GluingChangeCompBoundaryN H K H' K' α β)
  := gluing_change_comp_iso H K H' K' α β.

(** The cartesian image criterion retains only its local hypotheses. *)

Definition independent_gluing_cartesian {X Y : Gluing F} (h : Hom X Y)
    (HP : is_pullback (fmap K (fmap F (comma_right h)))
      (fmap K (comma_arrow Y)) (K (comma_left_ob X))
      (fmap K (comma_arrow X)) (fmap K (comma_left h)))
    (Hi : is_iso (α (comma_right_ob X)))
    (Hj : is_mono (α (comma_right_ob Y)))
  : (fmap (GluingChangeF H K α) h) ⦂ Cart(GluingRightF F')
  := gluing_change_pullback_cartesian H K α h HP Hi Hj.

End IndependentChange.

(** ** Reversed Category Levels

    Fix six separate base/target categories and compatible changes.
    The candidate preservation theorem uses only the supplied image square. *)

Section ReversedChange.
Universes
  o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5.
Constraint e0 < h0, h0 < o0, o0 < l0.
Constraint h1 < e1, e1 < o1, o1 < l1.
Constraint e2 < h2, h2 < o2, o2 < l2.
Constraint h3 < e3, e3 < o3, o3 < l3.
Constraint e4 < h4, h4 < o4, o4 < l4.
Constraint h5 < e5, e5 < o5, o5 < l5.
Constraint l5 < o4, l4 < o3, l3 < o2, l2 < o1, l1 < o0.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {C'' : Cat@{o4 h4 e4 l4 l4}}.
Context {D'' : Cat@{o5 h5 e5 l5 l5}}.
Context {F : Fct C D} {F' : Fct C' D'} {F'' : Fct C'' D''}.
Context (H : Fct C C') (K : Fct D D').
Context (H' : Fct C' C'') (K' : Fct D' D'').
Context (α : (K ∘F F) ⇒ (F' ∘F H))
    (β : (K' ∘F F') ⇒ (F'' ∘F H')).

(** The actual change functor accepts these strict boundaries. *)

Definition reversed_gluing_change
  : Fct (Gluing F) (Gluing F')
  := GluingChangeF H K α.

(** Both projections retain their separate ambient categories. *)

Definition reversed_gluing_projection
  : (GluingRightF F' ∘F GluingChangeF H K α) ≅N (H ∘F GluingRightF F)
  := gluing_change_base_iso H K α.

(** Composite compatibility uses all six category boundaries. *)

Definition reversed_gluing_composite
  : (GluingChangeF H' K' β ∘F GluingChangeF H K α) ≅N
      GluingChangeF (H' ∘F H) (K' ∘F K)
        (GluingChangeCompBoundaryN H K H' K' α β)
  := gluing_change_comp_iso H K H' K' α β.

(** The cartesian image criterion retains only its local hypotheses. *)

Definition reversed_gluing_cartesian {X Y : Gluing F} (h : Hom X Y)
    (HP : is_pullback (fmap K (fmap F (comma_right h)))
      (fmap K (comma_arrow Y)) (K (comma_left_ob X))
      (fmap K (comma_arrow X)) (fmap K (comma_left h)))
    (Hi : is_iso (α (comma_right_ob X)))
    (Hj : is_mono (α (comma_right_ob Y)))
  : (fmap (GluingChangeF H K α) h) ⦂ Cart(GluingRightF F')
  := gluing_change_pullback_cartesian H K α h HP Hi Hj.

End ReversedChange.

(** ** A Genuinely Monic Outgoing Boundary

    Start with the constant unit model on the walking arrow. Change it to
    the diagram selecting false from unit to booleans. The incoming
    boundary is identity; the outgoing boundary is monic but not invertible.
    Its image square is nevertheless cartesian by the weaker criterion. *)

Section MonicBoundary.

(** A chosen Boolean determines a respectful map from unit. *)

Program Definition unit_bool (b : bool)
  : UnitS →r BoolS
  :=
  {|func x := b
  |}.
Next Obligation. intros x y H. reflexivity. Defined.

(** Every such map is monic because maps into unit are specified-equal. *)

Definition unit_bool_mono (b : bool)
  : @is_mono SetCat UnitS BoolS (unit_bool b).
Proof. intros Q f g H x. exact tt. Defined.

(** Selecting false misses true, so this boundary has no inverse. *)

Example unit_false_not_iso
  : ¬ @is_iso SetCat UnitS BoolS (unit_bool false).
Proof. intros [g [Hl Hr]]. pose proof (Hr true) as Ht. discriminate Ht. Defined.

(** The original model is constant and introduces no pullback choices. *)

Definition UnitModelF
  : Fct ArrowShape SetCat
  := ConstF ArrowShape (C := SetCat) UnitS.

(** The changed model has distinct unit/Boolean endpoint carriers. *)

Definition MonoModelF
  : Fct ArrowShape SetCat
  := ArrowDiagram (C := SetCat) (unit_bool false).

(** The boundary is the supplied arrow-diagram transformation. *)

Program Definition MonoBoundaryN
  : (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF) ⇒
      (MonoModelF ∘F (@IdF ArrowShape))
  := @ArrowN SetCat
      (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF)
      (MonoModelF ∘F (@IdF ArrowShape)) id (unit_bool false) _.
Next Obligation. intros x. reflexivity. Defined.

(** Each base has the original identity structure arrow. *)

Program Definition UnitGluingOb (b : bool)
  : Gluing UnitModelF
  :=
  {|comma_left_ob := UnitS
  ; comma_right_ob := b
  ; comma_arrow := id
  |}.

(** The walking step and identity top give the source square. *)

Program Definition unit_gluing_step
  : Hom (UnitGluingOb false) (UnitGluingOb true)
  :=
  {|comma_left := id
  ; comma_right := arrow_step
  |}.
Next Obligation. intros x. exact tt. Defined.

(** The identity pullback is its complete cartesian witness. *)

Definition unit_gluing_step_cartesian
  : unit_gluing_step ⦂ Cart(GluingRightF UnitModelF)
  := gluing_pullback_cartesian UnitModelF unit_gluing_step pullback_id.

(** The incoming boundary has the transparent identity inverse. *)

Definition mono_boundary_source_iso
  : is_iso (MonoBoundaryN false).
Proof. exists id. split; apply comp_id_l. Defined.

(** The outgoing component is monic without being invertible. *)

Example mono_boundary_target_not_iso
  : ¬ is_iso (MonoBoundaryN true)
  := unit_false_not_iso.

(** The actual mapped arrow is cartesian using only these local inputs. *)

Definition monic_changed_cartesian
  : (fmap (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN)
      unit_gluing_step) ⦂ Cart(GluingRightF MonoModelF)
  := gluing_change_pullback_cartesian IdF IdF MonoBoundaryN
      unit_gluing_step
      (gluing_cartesian_pullback UnitModelF unit_gluing_step
        unit_gluing_step_cartesian)
      mono_boundary_source_iso (unit_bool_mono false).

(** The changed structure at the target actually computes false. *)

Example monic_changed_arrow_computes
  : comma_arrow (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN
      (UnitGluingOb true)) tt = false.
Proof. reflexivity. Defined.

(** The nonidentity walking base edge is retained by computation. *)

Example monic_changed_base_computes
  : comma_right (fmap
      (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN)
      unit_gluing_step) = arrow_step.
Proof. reflexivity. Defined.

End MonicBoundary.

(** ** Failure without the Incoming Inverse

    Reverse the unit/Boolean diagram: the source boundary selects false
    and the target boundary is identity. The target functor is still
    identity, but the mapped source square is not cartesian. This guards
    against treating an arbitrary compatible change as cartesian. *)

Section MissingIncomingInverse.

(** The collapsing map supplies the opposite directed model diagram. *)

Program Definition bool_unit
  : BoolS →r UnitS
  :=
  {|func x := tt
  |}.

(** The alternative model sends the walking step from Boolean to unit. *)

Definition CollapseModelF
  : Fct ArrowShape SetCat
  := ArrowDiagram (C := SetCat) bool_unit.

(** Its compatible boundary has the noninvertible map at the source. *)

Program Definition CollapseBoundaryN
  : (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF) ⇒
      (CollapseModelF ∘F (@IdF ArrowShape))
  := @ArrowN SetCat
      (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF)
      (CollapseModelF ∘F (@IdF ArrowShape)) (unit_bool false) id _.
Next Obligation. intros x. exact tt. Defined.

(** A cone selecting true has no mediator through the constant false leg. *)

Example arbitrary_change_not_cartesian
  : ¬ ((fmap (GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      CollapseBoundaryN) unit_gluing_step) ⦂ Cart(GluingRightF CollapseModelF)).
Proof.
  intro Hc.
  pose (HP := gluing_cartesian_pullback CollapseModelF
    (fmap (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) CollapseBoundaryN)
      unit_gluing_step) Hc).
  assert (Hcone : fmap CollapseModelF arrow_step ∘ unit_bool true ≈
    comma_arrow (GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      CollapseBoundaryN (UnitGluingOb true)) ∘ id).
  { intros x. exact tt. }
  destruct (snd HP UnitS (unit_bool true) id Hcone) as [m [[H1 H2] Hu]].
  pose proof (H1 tt) as Ht. discriminate Ht.
Defined.

End MissingIncomingInverse.

(** ** Recovered Data through the Natural-Isomorphism Corollary

    Return to the original tagged lifting square. Identity model change
    preserves its pullback candidate. The newly transported cartesian
    witness computes a factor retaining both tagged coordinates. *)

Section TaggedTransport.

(** Identity compatibility is supplied as explicit natural data. *)

Definition TaggedBoundaryN
  : ((@IdF SetCat) ∘F IdF) ⇒ ((@IdF SetCat) ∘F IdF)
  := CommaChangeIdRightN IdF.

(** Retain a component inverse, without selecting any model limits. *)

Definition tagged_boundary_iso
  : TaggedBoundaryN ⦂ ((@IdF SetCat) ∘F IdF) ≅N ((@IdF SetCat) ∘F IdF).
Proof. intro X. exists id. split; apply comp_id_l. Defined.

(** The actual image is the original general change, not a second action. *)

Definition TaggedChangeF
  : Fct (Gluing (@IdF SetCat)) (Gluing (@IdF SetCat))
  := GluingChangeF IdF IdF TaggedBoundaryN.

(** Apply the isomorphism corollary with identity preservation of this cone. *)

Definition tagged_changed_cartesian
  : (fmap TaggedChangeF tagged_reindex_lift) ⦂ Cart(GluingRightF (@IdF SetCat))
  := gluing_change_cartesian_iso IdF IdF TaggedBoundaryN tagged_reindex_lift
      tagged_boundary_iso (λ HP, HP) tagged_reindex_cartesian.

(** The generic factor uses the transported cartesian witness. *)

Definition tagged_changed_factor
  : (@Hom (Gluing (@IdF SetCat))) (TaggedChangeF TaggedGluingObj)
      (TaggedChangeF TaggedReindexedOb)
  := cartesian_factor tagged_changed_cartesian
      (fmap TaggedChangeF tagged_gluing_toggle) id
      (@comp_id_r SetCat TaggedGluingS TaggedGluingS gluing_toggle).

(** Both original tagged coordinates survive the boundary transport. *)

Example tagged_changed_factor_computes
  : ((comma_left tagged_changed_factor (3, false)).1,
      (comma_left tagged_changed_factor (3, false)).2.1) =
      ((3, false), (3, true)).
Proof. reflexivity. Defined.

(** The prescribed base factor stays the original identity function. *)

Example tagged_changed_factor_base_computes
  : comma_right tagged_changed_factor (3, false) = (3, false).
Proof. reflexivity. Defined.

(** The map action respects the original nontrivial square equality. *)

Example tagged_change_respects
  : fmap TaggedChangeF tagged_gluing_toggle ≈ fmap TaggedChangeF id.
Proof. rewrite tagged_gluing_toggle_equal. reflexivity. Qed.

(** The change still retains the native tag-changing side function. *)

Example tagged_changed_map_computes
  : comma_left (fmap TaggedChangeF tagged_gluing_toggle) (3, false)
      = (3, true).
Proof. reflexivity. Defined.

End TaggedTransport.

(** ** Computation of the Model-Change Comparisons

    Use the same unit and monic-boundary models. Identity and composite
    comparisons reuse the general comma inverses, followed only by
    specified-equal left-boundary transport. *)

Section ComparisonComputation.

(** The identity-model comparison retains its inverse as data. *)

Definition UnitChangeIdIso
  : GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      (CommaChangeIdRightN UnitModelF) ≅N IdF
  := gluing_change_id_iso UnitModelF.

(** The identity comparison keeps the base object and its identity map. *)

Example unit_change_identity_computes
  : comma_right (UnitChangeIdIso.1 (UnitGluingOb false)) = tt.
Proof. reflexivity. Defined.

(** Its saved inverse computes the original unit element. *)

Example unit_change_identity_inverse_computes
  : comma_left ((UnitChangeIdIso.2 (UnitGluingOb false)).1) tt = tt.
Proof. reflexivity. Defined.

(** Compose the monic-boundary change with identity of its target model. *)

Definition MonoChangeCompIso
  : (GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      (CommaChangeIdRightN MonoModelF) ∘F
      GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN) ≅N
      GluingChangeF ((@IdF ArrowShape) ∘F IdF) ((@IdF SetCat) ∘F IdF)
        (GluingChangeCompBoundaryN IdF IdF IdF IdF MonoBoundaryN
          (CommaChangeIdRightN MonoModelF))
  := gluing_change_comp_iso IdF IdF IdF IdF MonoBoundaryN
      (CommaChangeIdRightN MonoModelF).

(** The composite comparison inverse preserves the endpoint base value. *)

Example monic_composite_inverse_computes
  : comma_right ((MonoChangeCompIso.2 (UnitGluingOb true)).1) = tt.
Proof. reflexivity. Defined.

(** A transported pullback token remains a Type-valued pair with its
    original Boolean equality witness. *)

Definition tagged_changed_token
  : comma_left_ob (TaggedChangeF TaggedReindexedOb)
  := tagged_pullback_token.

(** Inspecting the unchanged witness needs no proof irrelevance. *)

Example tagged_changed_token_computes
  : snd tagged_changed_token.2.2 = true.
Proof. reflexivity. Defined.

End ComparisonComputation.
