From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import
  Algebra
  Commands.

(** * Witness sharing in parent order

    The ordinary parent contributes an unkeyed [HasFlag]. The virtual
    parent contributes two occurrences of the same class with distinct keys. *)

Minks.Struct KeyedFlags
  extends TwoFlags
  exports BothFlags [carrier].

Minks.Mixin PlainFirst (A : Type)
  extends HasFlag, BothFlags A
  :=
  { plain_and_left : @flag hasFlag = @flag (@BothFlags_leftFlag A bothFlags)
  ; plain_and_right : bool * bool :=
      (@flag hasFlag, @flag (@BothFlags_rightFlag A bothFlags))
  }.

Check @PlainFirst : ∀ (A : Type) (left right : HasFlag), Type.

(** The constructor accepts reflexivity for the left flag even when the
    right flag computes to a different boolean. *)

Example plain_shares_only_left (A : Type)
  : @plain_and_right A {| flag := true |} {| flag := false |}
      (@Build_PlainFirst A {| flag := true |} {| flag := false |} eq_refl)
    = (true, false)
  := eq_refl.

Fail Minks.Mixin KeyedFirst (A : Type)
  extends BothFlags A, HasFlag
  := { keyed_first_law : True }.

(** Repeating the same parent contributes one witness. *)

Minks.Mixin RepeatedPoint (A : Type)
  extends HasPoint A, HasPoint A, HasPoint A
  := { repeated_value : A := @point A hasPoint }.

Check @RepeatedPoint : ∀ A : Type, HasPoint A → Type.
Fail Minks.Mixin IncompatiblePoints (A B : Type)
  extends HasPoint A, HasPoint B
  := { unused_points : True }.

(** Each parent may use a witness introduced by an earlier parent. *)

Minks.Mixin AtPoint (P : HasPoint nat)
  := { selected_zero : @point nat P = 0 }.

Minks.Mixin AtValue (n : nat)
  := { value_zero : n = 0 }.

Minks.Mixin PointLaws
  extends HasPoint nat, AtPoint hasPoint, AtValue point,
          AtPoint ltac:(exact hasPoint)
  := { point_laws : True }.

Check @PointLaws : ∀ P : HasPoint nat,
  AtPoint P → AtValue (@point nat P) → Prop.

Minks.Mixin OuterPointLaws (outer : HasPoint nat)
  extends HasPoint nat, AtPoint outer, AtValue (@point nat hasPoint)
  := { outer_point_laws : True }.

Check @OuterPointLaws : ∀ (outer inner : HasPoint nat),
  AtPoint outer → AtValue (@point nat inner) → Prop.

Fail Minks.Mixin ForwardPoint
  extends AtPoint hasPoint, HasPoint nat
  := { forward_point : True }.

Fail Minks.Mixin ForwardValue
  extends AtValue point, HasPoint nat
  := { forward_value : True }.

(** Two convertible applications index the same component in different exports.
    Rocq checks the shared point by conversion when both are inherited. *)

Module ConvertiblePoints.
Record Label := { element : Type }.

Definition values (L : Label)
  := option (element L).
Definition values_alias
  := values.

Minks.Struct Chosen (A : Type)
  with  hasPoint : HasPoint [A].

Minks.Struct FlagOnly
  with  extra : HasFlag.

Module Left.
Minks.Struct Choice (L : Label)
  extends Chosen (values L)
  exports LeftPoint [].

Minks.Struct FlaggedChoice (L : Label)
  extends FlagOnly, Chosen (values L).
End Left.

Module Right.
Minks.Struct Choice (L : Label)
  extends Chosen (values_alias L)
  exports RightPoint [].
End Right.

Minks.Mixin DirectPoint (L : Label)
  extends HasPoint (values L), HasPoint (values_alias L)
  := { direct_value : values L := @point _ hasPoint }.

Check @DirectPoint : ∀ L, HasPoint (values L) → Type.
Fail Minks.Mixin IllTypedPoint (L : Label)
  extends HasPoint (Some L)
  := { bad_value : True }.
Fail Minks.Struct IllTypedChoice (L : Label)
  extends Chosen (Some L).

(** A global in an ordinary argument keeps its meaning when an inherited
    witness would otherwise be given the same name. *)

Module PointIndex.
Definition hasPoint := bool.
Minks.Mixin IndexedPoint
  extends HasPoint hasPoint
  := { indexed_value : hasPoint := point }.
Check @IndexedPoint : HasPoint bool → Type.
End PointIndex.

(** Rocq infers the lambda domain from the preceding named argument.
    A further child inherits the same function after index substitution. *)

Minks.Mixin HasFixed {A : Type} (f : A → A)
  := { fixed : A; fixed_law : f fixed = fixed }.

Minks.Mixin OptionFixed (L : Label)
  extends HasFixed (A := values L) (fun x => x)
  := { option_fixed_law : True }.

Minks.Mixin NestedFixed (A : Type)
  extends OptionFixed (Build_Label A)
  := { nested_fixed_law : True }.

Check @NestedFixed : ∀ A (F : @HasFixed (option A) (fun x => x)),
  @OptionFixed (Build_Label A) F → Type.

Minks.Struct FixedFunction {A : Type} (f : A → A)
  with  hasFixed : HasFixed [A, f].

Minks.Struct IdentityFixed (L : Label)
  extends FixedFunction (A := values L) (fun x => x).

Example fixed_parent (L : Label) (F : IdentityFixed L)
  : IdentityFixed_hasFixed L F =
      FixedFunction_hasFixed (fun x : values L => x)
        (IdentityFixedToFixedFunction L F)
  := eq_refl.

Section ChosenFunction.
  Variable A : Type.
  Minks.Struct IdentityChoice
    extends Chosen (A → A).
End ChosenFunction.

Check @MakeIdentityChoice : ∀ A : Type, HasPoint (A → A) → IdentityChoice A.

(** The header parameter precedes the witness even when the tactic uses it
    to produce a closed index. *)

Minks.Mixin ClosedPoint (n : nat)
  extends HasPoint ltac:(let t := type of n in exact t)
  := { closed_point : nat := @point nat hasPoint }.

Check @ClosedPoint : nat → HasPoint nat → Type.

Fail Minks.Mixin DistinctTacticPoints
  extends HasPoint ltac:(exact nat), HasPoint ltac:(exact bool)
  := { incompatible : True }.

(** A relative parent's assembled view is available at the next parent.
    The public telescope retains only its selected component. *)

Minks.Mixin AtChoice (L : Label) (c : Left.LeftPoint L)
  := { chosen_value : values L := @point _ (Left.LeftPoint_hasPoint L c) }.

Minks.Mixin LaterChoice (L : Label)
  extends Left.LeftPoint L, AtChoice L leftPoint
  := { later_choice : True }.

Check @LaterChoice : ∀ L (P : HasPoint (values L)),
  AtChoice L (Left.MakeLeftPoint L P) → Prop.

Minks.Mixin SharedPoint (L : Label)
  extends Left.LeftPoint L, Right.RightPoint L, Left.LeftPoint L
  :=
  { left_value : values L := @point _ (Left.LeftPoint_hasPoint L leftPoint)
  ; right_value : values L := @point _ (Right.RightPoint_hasPoint L rightPoint)
  }.

Check @SharedPoint : ∀ L, HasPoint (values L) → Type.

Example shared_value (L : Label) (P : HasPoint (values L))
  : @left_value L P (@Build_SharedPoint L P) =
    @right_value L P (@Build_SharedPoint L P)
  := eq_refl.

Fail Minks.Mixin DifferentLabels (L K : Label)
  extends Left.LeftPoint L, Right.RightPoint K
  := { unused_labels : True }.
(** Both parents contribute the point at convertible indices. It precedes
    the flag from the left parent and is fixed by the bare export. *)

Import Left Right.
Minks.Struct BothChoices (L : Label)
  extends Left.FlaggedChoice L, Right.Choice L
  exports CommonChoice, FixedChoice [hasPoint].

Check @MakeBothChoices : ∀ L, HasPoint (values L) → HasFlag → BothChoices L.
Check @MakeCommonChoice
  : ∀ (L : Label) (P : HasPoint (values L)), HasFlag → CommonChoice L P.
Check @MakeFixedChoice
  : ∀ (L : Label) (P : HasPoint (values L)), HasFlag → FixedChoice L P.
End ConvertiblePoints.

(** * Fresh dependent fields from an export

    The pair in the second exported slot depends twice on the flag in
    the first slot, even when compatible older fields are in scope. *)

Minks.Struct DiagonalFlag
  extends OneFlag
  exports HasDiagonalFlag [carrier].

Minks.Struct ThirdDiagonal
  extends TwoFlags
  with  [thirdFlag, diagonal] : HasDiagonalFlag.

Check ThirdDiagonal_diagonal
  : ∀ F : ThirdDiagonal, FlagPair (ThirdDiagonal_thirdFlag F) (ThirdDiagonal_thirdFlag F).

Fail Minks.Struct DuplicateDiagonal
  extends OneFlag
  with  : HasDiagonalFlag.

(** * Dependency closure of a fixed selection

    Fixing multiplication also fixes its equivalence and carrier. The
    selected point remains a field and survives extraction and packing. *)

Minks.Struct FixedMultiplication
  extends PointedMagma
  exports PointOnMultiplication [hasMagma],
          PointOnPackedMagma [Magma].

Check @PointOnMultiplication
  : ∀ (A : Type) (E : HasEquiv A) (M : @HasMagma A E), Type.

Example repack_selected_point (A : Type) (E : HasEquiv A)
    (M : @HasMagma A E) (P : HasPoint A)
  : FixedMultiplication_hasPoint
      (FixedMultiplicationOfPointOnMultiplication A E M
        (MakePointOnMultiplication A E M P)) = P
  := eq_refl.

(** Fixing the same multiplication through its packed magma extracts
    definitionally the same remaining point. *)

Example fixed_presentations_agree (F : FixedMultiplication)
  : PointOnPackedMagma_hasPoint (FixedMultiplicationToPointOnPackedMagma F)
    = PointOnMultiplication_hasPoint (FixedMultiplicationToPointOnMultiplication F)
  := eq_refl.

Fail Minks.Struct DuplicateFix
  extends PointedMagma
  exports DuplicatePoint [hasPoint, hasPoint].

(** * Composing relative interfaces over a specified magma

    The operations come from the supplied magma. The point and both
    law witnesses are the components of its relative monoid interface. *)

Minks.Mixin IsIdempotentMonoid (M : Magma)
  extends IsMonoid M
  := { mul_idem : ∀ x : M, x * x ≈ x }.

Check @IsIdempotentMonoid
  : ∀ (M : Magma), IsSemigroup M → ∀ P : HasPoint M,
      IsUnitAt M (hasPoint := P) → Type.

(** Both parents select the same magma. Repeating the monoid interface
    shares its three fields, including the point used by its unit laws. *)

Minks.Mixin IsSingletonMonoid (M : Magma)
  extends IsIdempotentMonoid M, IsMonoid M
  := { all_equiv : ∀ x y : M, x ≈ y }.

Check @IsSingletonMonoid
  : ∀ (M : Magma) (A : IsSemigroup M) (P : HasPoint M)
      (U : IsUnitAt M (hasPoint := P)), @IsIdempotentMonoid M A P U → Type.

Fail Minks.Mixin DifferentMonoids (M N : Magma)
  extends IsIdempotentMonoid M, IsMonoid N
  := { different_monoids : True }.

(** Expand the relative monoid interface at the specified magma. *)

Section AtMagma.
Context (M : Magma).

Minks.Struct MonoidOnMagma
  with  : IsMonoid [M].

Variable N : Magma.
Fail Minks.Struct ConflictingBases
  with  : IsMonoid [M],
        : IsMonoid [N].
End AtMagma.

Example assembled_monoid_on_magma (M : Magma)
    (A : IsSemigroup M) (P : HasPoint M) (U : IsUnitAt M (hasPoint := P))
  : let S := MakeMonoidOnMagma M A P U in
    MakeIsMonoid M (MonoidOnMagma_isSemigroup M S) (MonoidOnMagma_hasPoint M S)
      (MonoidOnMagma_isUnitAt M S) = MakeIsMonoid M A P U
  := eq_refl.

(** The discharged fields retain their projection paths when the parent
    parameter changes name. A further mixin consumes those exact fields. *)

Section InheritedMagma.
Context (N : Magma).

Minks.Struct IdempotentOnMagma
  extends MonoidOnMagma N
  with  idempotent : IsIdempotentMonoid [N, isSemigroup, hasPoint, isUnitAt].
End InheritedMagma.

Check @IdempotentOnMagmaOfMonoidOnMagma
  : ∀ (N : Magma) (S : MonoidOnMagma N),
      @IsIdempotentMonoid N (MonoidOnMagma_isSemigroup N S)
        (MonoidOnMagma_hasPoint N S) (MonoidOnMagma_isUnitAt N S)
      → IdempotentOnMagma N.
