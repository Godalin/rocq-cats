From Cats Require Import
  Instance.Set.PresheafRegionUnion
  Instance.Set.Simplicial.Core
  Instance.Bool.Group
  Cat.Diagram.Core
  Cat.Core.
From Stdlib Require Import Lia.

Import Cats.Cat.Core.
Local Open Scope nat_scope.

(** * Genuine Overlap with Retained Representatives

    A value is a natural number with a Boolean tag. Specified equality
    compares only the number. The two regions cover numbers at most one
    and at least one, respectively; each retains a further Boolean witness.
    Their maps agree on the overlap, but return native-distinct tags. *)

Program Definition TaggedS
  : SetC
  :=
  {|carrier := (nat * bool)%type
  ; carrier_equiv x y := fst x = fst y
  |}.
Next Obligation. split; red; intros; congruence. Defined.

Definition Q
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) TaggedS.

Program Definition LeftRegion
  : PresheafRegion Q
  :=
  {|region_member X x := ((fst x <= 1) * bool)%type
  ; region_precomp X Y f x H := H
  |}.
Next Obligation.
  intros x y E. change (fst x = fst y) in E.
  split; intros [H t]; split; [lia | exact t | lia | exact t].
Defined.

Program Definition RightRegion
  : PresheafRegion Q
  :=
  {|region_member X x := ((1 <= fst x) * bool)%type
  ; region_precomp X Y f x H := H
  |}.
Next Obligation.
  intros x y E. change (fst x = fst y) in E.
  split; intros [H t]; split; [lia | exact t | lia | exact t].
Defined.

Program Definition left_map
  : RegionPsh LeftRegion ⇒ Q
  :=
  {|nt X := {|func x := (fst x.1, false)|}
  |}.
Next Obligation. intros x y E. exact E. Defined.
Next Obligation. intros x. reflexivity. Defined.

Program Definition right_map
  : RegionPsh RightRegion ⇒ Q
  :=
  {|nt X := {|func x := (fst x.1, true)|}
  |}.
Next Obligation. intros x y E. exact E. Defined.
Next Obligation. intros x. reflexivity. Defined.

Definition overlap_agreement
  : (left_map ∘Nv RegionInterLeftN LeftRegion RightRegion) ≈N
      (right_map ∘Nv RegionInterRightN LeftRegion RightRegion).
Proof. intros X x. reflexivity. Defined.

Definition glued
  : RegionPsh (RegionUnion LeftRegion RightRegion) ⇒ Q
  := RegionUnionGluingN LeftRegion RightRegion left_map right_map
      overlap_agreement.

Definition left_value (n : nat) (H : n <= 1) (tag witness : bool)
  : RegionPsh (RegionUnion LeftRegion RightRegion) 0
  := ((n, tag); inl (H, witness)).

Definition right_value (n : nat) (H : 1 <= n) (tag witness : bool)
  : RegionPsh (RegionUnion LeftRegion RightRegion) 0
  := ((n, tag); inr (H, witness)).

(** Actual descent computes different values on the two sides. *)

Example nonconstant_gluing
  : (glued 0 (left_value 0 (ltac:(lia)) true false),
     glued 0 (right_value 3 (ltac:(lia)) false true)) =
      ((0, false), (3, true)).
Proof. vm_compute. reflexivity. Defined.

(** Equal underlying values with different branches and witnesses may
    compute native-distinct representatives. *)

Example overlap_outputs
  : (glued 0 (left_value 1 (ltac:(lia)) true false),
     glued 0 (right_value 1 (ltac:(lia)) false true)) =
      ((1, false), (1, true)).
Proof. vm_compute. reflexivity. Defined.

Definition actual_gluing_proper
  : glued 0 (left_value 1 (ltac:(lia)) true false) ≈S
      glued 0 (right_value 1 (ltac:(lia)) false true).
Proof. apply func_proper. reflexivity. Defined.

Definition left_recovery
  := region_union_gluing_β1 LeftRegion RightRegion left_map right_map
      overlap_agreement.

Definition right_recovery
  := region_union_gluing_β2 LeftRegion RightRegion left_map right_map
      overlap_agreement.

Definition actual_pushout
  := region_union_pushout LeftRegion RightRegion.

(** Membership witnesses remain available even though equality ignores them. *)

Definition retained_witness
    (x : RegionPsh (RegionUnion LeftRegion RightRegion) 0)
  : bool
  := match x.2 with inl H => snd H | inr H => snd H end.

Example membership_is_retained
  : (retained_witness (left_value 1 (ltac:(lia)) true false),
     retained_witness (right_value 1 (ltac:(lia)) false true)) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Fail Definition outputs_are_native_equal
  : glued 0 (left_value 1 (ltac:(lia)) true false) =
      glued 0 (right_value 1 (ltac:(lia)) false true)
  := eq_refl.

(** ** Incompatible Maps Have No Mediator

    The two constant Boolean maps disagree at the actual overlap value one.
    Their two recovery equations would force false and true to be equal. *)

Definition B
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) BoolS.

Program Definition false_map
  : RegionPsh LeftRegion ⇒ B
  := {|nt X := {|func x := false|}|}.
Next Obligation. intros x y E. reflexivity. Defined.
Next Obligation. intros x. reflexivity. Defined.

Program Definition true_map
  : RegionPsh RightRegion ⇒ B
  := {|nt X := {|func x := true|}|}.
Next Obligation. intros x y E. reflexivity. Defined.
Next Obligation. intros x. reflexivity. Defined.

Definition incompatible_maps_do_not_glue
    (h : RegionPsh (RegionUnion LeftRegion RightRegion) ⇒ B)
    (L : (h ∘Nv RegionUnionLeftN LeftRegion RightRegion) ≈N false_map)
    (R : (h ∘Nv RegionUnionRightN LeftRegion RightRegion) ≈N true_map)
  : Empty_set.
Proof.
  pose (x := ((1, false); (le_n 1, false)) : RegionPsh LeftRegion 0).
  pose (y := ((1, true); (le_n 1, true)) : RegionPsh RightRegion 0).
  pose proof (@func_proper _ _ (h 0)
    (RegionUnionLeftN LeftRegion RightRegion 0 x)
    (RegionUnionRightN LeftRegion RightRegion 0 y) eq_refl) as E.
  pose proof (L 0 x) as EL. pose proof (R 0 y) as ER.
  change (h 0 (RegionUnionLeftN LeftRegion RightRegion 0 x) = false) in EL.
  change (h 0 (RegionUnionRightN LeftRegion RightRegion 0 y) = true) in ER.
  rewrite EL, ER in E. discriminate E.
Defined.

Fail Definition pushouts_are_implicitly_enabled
  : HasPushout (FctCat (Δ^op) SetCat)
  := ltac:(typeclasses eauto).
