From MinksTests Require Import ComponentInference.

Set Universe Polymorphism.

(** All reverse packers and additional search hints in this file are local. *)

Module Diamond.
Import JointDependency.

Section ForwardOnly.
Context (P : BCD) `{E : !HasE P}.
Definition available_interface : HasBCDE P := _.
Fail Definition automatic : BCDE := P.
End ForwardOnly.

(** Each immediate parent supplies its own fixed B and C. *)

Section BothParents.
#[local] Canonical extend_d (P : BCD) `{E : !HasE P}
  : BCDE := BCDEOfBCD P E.
#[local] Canonical extend_e (P : BCE) `{D : !HasD P}
  : BCDE := BCDEOfBCE P D.

Section Left.
Context (P : BCD).
Timeout 3 Fail Definition missing : BCDE := P.
Context `{E : !HasE P}.
Definition left : BCDE := P.
Example exact_left : left = BCDEOfBCD P E := eq_refl.
End Left.

Section Right.
Context (P : BCE).
Timeout 3 Fail Definition missing_right : BCDE := P.
Context `{D : !HasD P}.
Definition right : BCDE := P.
Example exact_right : right = BCDEOfBCE P D := eq_refl.
End Right.

Section Compatible.
Context (X : Type) (B : HasB X) (C : HasC X)
  (D : @HasD X B C) (E : @HasE X B C).
Example same_child
  : @left (MakeBCD X B C D) E = @right (MakeBCE X B C E) D
  := eq_refl.
End Compatible.

Section FromInterface.
Context (P : BCD) `{R : !HasBCE P}.
Timeout 3 Fail Definition unrelated_inputs : BCDE := P.
End FromInterface.

Section InterfaceSource.
Context (X : Type) `{Q : !HasBCDE X}.
Let P : BCD := BCDOfHasBCD X (_ : HasBCD X).
Definition from_interface : BCDE := P.
Example from_interface_fields : from_interface = BCDEOfHasBCDE X Q := eq_refl.
End InterfaceSource.

(** Rocq can follow either annotated intermediate. A cast straight from BC
    requests a different canonical projection. *)

Section Chain.
#[local] Canonical d_on_base (P : BC) `{D : !HasD P} : BCD := BCDOfBC P D.
#[local] Canonical e_on_base (P : BC) `{E : !HasE P} : BCE := BCEOfBC P E.
Context (P : BC) `{D : !HasD P}.
Timeout 3 Fail Definition missing_last : BCDE := (P : BCD).
Context `{E : !HasE P}.
Fail Definition from_base : BCDE := P.
Definition via_d : BCDE := (P : BCD).
Definition via_e : BCDE := (P : BCE).
Example diamond : via_d = via_e := eq_refl.
End Chain.

(** Two registrations with the same projection keys compete. Promote the
    native warning to an error here so the collision is checked. *)

Section Collision.
Local Set Warnings "+redundant-canonical-projection".
Fail #[local] Canonical from_intermediate (P : BC) `{D : !HasD P} `{E : !HasE P}
  : BCDE := BCDEOfBCD (BCDOfBC P D) E.
End Collision.
End BothParents.

Section DirectAncestor.
#[local] Canonical flat_child (P : BC) `{D : !HasD P} `{E : !HasE P}
  : BCDE := MakeBCDE P (BC_left P) (BC_right P) D E.
Context (P : BC) `{D : !HasD P}.
Timeout 3 Fail Definition missing_e : BCDE := P.
Context `{E : !HasE P}.
Definition direct : BCDE := P.
Example exact_direct : direct = BCDEOfBCD (BCDOfBC P D) E := eq_refl.
End DirectAncestor.
Section Competing.
#[local] Canonical packed_on_interface (X : Type) `{S : !HasBCDE X}
  : BCDE := BCDEOfHasBCDE X S.
#[local] Hint Cut [_* (BCDE_left | BCDE_right | BCDE_jointD | BCDE_jointE |
  BCDEToHasBCDE) MakeHasBCDE] : typeclass_instances.
Context (X : Type) (B0 B1 : HasB X) (C0 C1 : HasC X).
Section Shared.
Context `{D00 : !@HasD X B0 C0} `{E00 : !@HasE X B0 C0}
  `{D10 : !@HasD X B1 C0} `{E01 : !@HasE X B0 C1}.
Timeout 3 Definition resolved : BCDE := X.
Example selected_tuple : resolved = MakeBCDE X B0 C0 D00 E00 := eq_refl.
Example same_resolution : resolved = BCDEOfHasBCDE X (_ : HasBCDE X) := eq_refl.
End Shared.
Section Disjoint.
Context `{D00 : !@HasD X B0 C0} `{D11 : !@HasD X B1 C1}
  `{E01 : !@HasE X B0 C1} `{E10 : !@HasE X B1 C0}.
Definition left_view : HasBCD X := _.
Definition right_view : HasBCE X := _.
Timeout 3 Fail Definition joint_interface : HasBCDE X := _.
Timeout 3 Fail Definition joint_pack : BCDE := X.
End Disjoint.
End Competing.
End Diamond.

Module DistinctKeys.
Import Repeated Overlap.
Section Selection.
#[local] Canonical two_from_class (X : Type) `{Q : !TwoChoices X}
  : Two := TwoOfTwoChoices X Q.
Context (X : Type) `{P : !HasA X}.
Timeout 3 Fail Definition no_duplicate : Two := X.
Context `{Q : !TwoChoices X}.
Definition both : Two := X.
Example keep_left : Two_leftPoint both = TwoChoices_leftPoint Q := eq_refl.
Example keep_right : Two_rightPoint both = TwoChoices_rightPoint Q := eq_refl.
End Selection.
End DistinctKeys.

Module Recursive.
Import RecursiveAssembly.
Section Packing.
#[local] Canonical pack_on_type (X : Type) `{S : !Choices X}
  : Pack := PackOfChoices X S.
#[local] Hint Cut [_* (Pack_choice | PackToChoices) MakeChoices]
  : typeclass_instances.
#[local] Instance product_choice {X : Type} `{S : !Choices X}
  : Choice (X * X) :=
  let x := @chosen X (Choices_choice S) in Build_Choice _ (x, x).
Context (X : Type).
Timeout 3 Fail Definition no_leaf : Pack := ((X * X) * (X * X))%type.
Context `{P : !Choice X}.
Definition nested : Pack := ((X * X) * (X * X))%type.
Example exact_leaf :
  let x := @chosen X P in
  @chosen _ (Pack_choice nested) = ((x, x), (x, x)) := eq_refl.

Section Overcut.
#[local] Hint Cut [_* MakeChoices _* MakeChoices] : typeclass_instances.
Timeout 3 Fail Definition blocked_nested : Pack := ((X * X) * (X * X))%type.
End Overcut.
End Packing.
End Recursive.

Module SelectedSource.
Import RecursiveAssembly.
Definition raw : Choice unit := Build_Choice unit tt.
#[local] Hint Mode Choices + : typeclass_instances.
#[local] Canonical candidate := MakePack unit raw.
Definition inferred_native : Choices unit := _.
Example native_selection : inferred_native = PackToChoices candidate := eq_refl.

#[local] Remove Hints Pack_choice PackToChoices : typeclass_instances.

(** An alternative policy makes a concrete pack discoverable only through
    its selected carrier projection. Compare both outcomes on [unit]. *)

Ltac project_selected carrier project :=
  let index := eval cbn in carrier in
  lazymatch index with
  | Pack_carrier ?p => tryif has_evar p then fail else exact (project p)
  end.
#[local] Hint Extern 1 (Choice ?X) =>
  project_selected X Pack_choice : typeclass_instances.
#[local] Hint Extern 1 (Choices ?X) =>
  project_selected X PackToChoices : typeclass_instances.
Timeout 3 Fail Definition no_new_pack : Choices unit := _.
Timeout 3 Fail Definition no_new_field : Choice unit := _.

Section Known.
Context (p : Pack).
Definition known_group : Choices p := _.
Definition known_field : Choice p := _.
Example from_known : known_group = PackToChoices p := eq_refl.
Example from_known_field : known_field = Pack_choice p := eq_refl.
End Known.
Definition parent_group (p : Pack)
  : Choices (TypeCarrier_carrier (PackToTypeCarrier p))
  := _.
Example from_parent (p : Pack)
  : parent_group p = PackToChoices p
  := eq_refl.
Timeout 3 Fail Definition unknown : {X : Type & Choices X}
  := existT Choices _ _.

End SelectedSource.

From MinksExamples Require Import Algebra.

Module SelectedMonoid.
#[local] Canonical group_on_monoid (M : Monoid) `{R : !IsGroup M}
  : Group := GroupOfIsGroup M R.
Local Arguments GroupOfMonoid _ {_}.

Section WrongChoices.
Context (M : Monoid) `{R : !HasGroup M}.
Timeout 3 Fail Definition different_monoid : Group := M.
End WrongChoices.

Section RelativeEvidence.
Context (M : Monoid) `{R : !IsGroup M}.
Definition from_relative : Group := M.
Example stored_relative
  : Group_hasInverse from_relative = IsGroup_hasInverse R
  := eq_refl.
End RelativeEvidence.

Section SelectedParent.
Context (M : Monoid).
Timeout 3 Fail Definition missing_atom : HasInverse M := _.
Timeout 3 Fail Definition missing_relative : IsGroup M := _.
Timeout 3 Fail Definition missing_group_interface : HasGroup M := _.
Timeout 3 Fail Definition missing_packed : Group := M.

Context `{I : !HasInverse M}.
Definition automatic : Group := M.
Definition named : Group := GroupOfMonoid M.
Definition explicit_choice (J : HasInverse M) : Group := @GroupOfMonoid M J.
Definition on_carrier : HasGroup M := _.
Example same_packing : automatic = named := eq_refl.
Example selected_inverse : Group_hasInverse automatic = I := eq_refl.
Example selected_component : HasGroup_hasInverse on_carrier = I := eq_refl.
Example alternate_inverse (J : HasInverse M)
  : Group_hasInverse (explicit_choice J) = J := eq_refl.
End SelectedParent.

(** Search terminates in both cases. Registering a concrete canonical pack
    still lets extraction select it from just the carrier. *)

Section ConcreteCandidate.
Context (model : unit -> HasGroup unit).
Timeout 3 Fail Definition bare_carrier : HasGroup unit := _.
#[local] Canonical unit_group := GroupOfHasGroup unit (model tt).
Definition inferred_on_unit : HasGroup unit := _.
Example extracted_candidate
  : inferred_on_unit = GroupToHasGroup unit_group := eq_refl.
End ConcreteCandidate.
End SelectedMonoid.

Module BareCarrier.
(** The carrier in the loop is already a rigid variable. The accompanying
    comparison records the outcome of enabling each cut separately. *)

#[local] Canonical monoid_on_type (A : Type) `{H : !HasMonoid A}
  : Monoid := MonoidOfHasMonoid A H.
#[local] Canonical group_on_type (A : Type) `{H : !HasGroup A}
  : Group := GroupOfHasGroup A H.

#[local] Hint Cut [_*
  (Group_hasInverse | Group_hasMagma | Group_hasEquiv | Group_hasPoint |
   Group_isUnitAt | Group_isSemigroup | GroupToHasGroup | GroupToIsGroup)
  MakeHasGroup] : typeclass_instances.
#[local] Hint Cut [_*
  (Monoid_hasEquiv | Monoid_hasMagma | Monoid_isSemigroup | Monoid_hasPoint |
   Monoid_isUnitAt | MonoidToHasMonoid | MonoidToIsMonoid | MonoidToIsMonoidWithPoint)
  MakeHasMonoid] : typeclass_instances.

Timeout 3 Fail Definition no_index : {A : Type & HasGroup A}
  := existT HasGroup _ _.
Timeout 3 Fail Definition no_ground_model : HasGroup unit := _.

Section Missing.
Context (A : Type).
Timeout 3 Fail Definition no_monoid : Monoid := A.
Timeout 3 Fail Definition no_group : Group := A.
Timeout 3 Fail Definition no_monoid_class : HasMonoid A := _.
Timeout 3 Fail Definition no_group_class : HasGroup A := _.
Timeout 3 Fail Definition no_point : HasPoint A := _.
Timeout 3 Fail Definition no_equiv : HasEquiv A := _.
Context `{H : !HasMonoid A}.
Definition from_monoid_interface : Monoid := A.
Example uses_monoid_interface
  : from_monoid_interface = MonoidOfHasMonoid A H
  := eq_refl.
Timeout 3 Fail Definition missing_inverse : HasGroup A := _.
Timeout 3 Fail Definition missing_pack : Group := A.
Context `{I : !HasInverse A}.
Definition completed : Group := A.
Definition assembled : HasGroup A := _.
Example exact_inverse : Group_hasInverse completed = I := eq_refl.
Example exact_view : completed = GroupOfHasGroup A assembled := eq_refl.
Example same_parent
  : GroupToMonoid completed = from_monoid_interface
  := eq_refl.
Context `{J : !HasInverse A}.
Definition other_completion : Group := A.
Example local_inverse : Group_hasInverse other_completion = J := eq_refl.
Example explicit_inverse
  : Group_hasInverse (GroupOfMonoid (MonoidOfHasMonoid A H) I) = I := eq_refl.
End Missing.

Section GivenInterface.
Context (A : Type) `{G : !HasGroup A}.
Definition from_group_class : Group := A.
Fail Definition cast_class_value : Group := G.
Example from_exact : from_group_class = GroupOfHasGroup A G := eq_refl.
Definition from_weaker_class : Monoid := A.
Example weaken_exact
  : Monoid_hasMagma from_weaker_class = HasGroup_hasMagma G
  := eq_refl.
End GivenInterface.

Section ExistingPack.
Context (G : Group).
Definition extracted : HasGroup G := _.
Example keep_extraction : extracted = GroupToHasGroup G := eq_refl.
Example keep_projection : (_ : HasInverse G) = Group_hasInverse G := eq_refl.
End ExistingPack.

(** A separately registered wrapper has its own hint name. The source term
    computes to the same projection, but the search trace takes a new edge. *)

Section ForwardedProjection.
#[local] Instance forwarded_inverse (G : Group) : HasInverse G := Group_hasInverse G.
#[local] Hint Cut [_* forwarded_inverse MakeHasGroup] : typeclass_instances.
Context (A : Type) `{H : !HasMonoid A}.
Timeout 3 Fail Definition missing_forwarded : HasGroup A := _.
Context `{I : !HasInverse A}.
Definition with_inverse : Group := A.
Example forwarded_exact : Group_hasInverse with_inverse = I := eq_refl.
End ForwardedProjection.

Section MixedPackers.
#[local] Canonical group_on_parent (M : Monoid) `{R : !IsGroup M}
  : Group := GroupOfIsGroup M R.
Context (M : Monoid).
Timeout 3 Fail Definition no_relative : Group := M.
Context `{I : !HasInverse M}.
Definition from_parent : Group := M.
Example from_exact_inverse : Group_hasInverse from_parent = I := eq_refl.
End MixedPackers.
End BareCarrier.

(** Closing the experiments restores the ordinary Class-only behavior. *)

Section AfterExperiments.
Context (M : Monoid) `{I : !HasInverse M}.
Definition inferred_interface : IsGroup M := _.
Fail Definition inferred_pack : Group := M.
End AfterExperiments.
