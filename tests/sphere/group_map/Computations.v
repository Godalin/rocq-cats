From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereGroupMap
  Instance.Bool.CocycleSphereGroup
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Mapping Need Not Preserve Chosen Fillers

    In this constant simplicial setoid every equality has Boolean
    witnesses. Negation changes native representatives; choices can
    independently return false or true. Commuting squares must therefore
    use generated equality, not native equality or identical choices. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation.
  split.
  - intros x. exact true.
  - intros x y E. exact E.
  - intros x y z E F. exact E.
Defined.

(** A constant simplicial object retains those representations in every degree. *)

Definition WitnessX
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Program Definition flip_resp
  : WitnessS →r WitnessS
  :=
  {|func := negb
  |}.
Next Obligation. intros x y E. exact E. Defined.

(** The same negation in each degree is a natural transformation. *)

Program Definition FlipN
  : WitnessX ⇒ WitnessX
  :=
  {|nt n := flip_resp
  |}.
Next Obligation. intros x. exact true. Defined.

(** Retain its actual inverse map; inverse laws use the Boolean relation. *)

Definition flip_NatIso
  : FlipN ⦂ WitnessX ≅N WitnessX.
Proof. intros n. exists flip_resp. split; intros x; exact true. Defined.

(** Every prescribed Boolean is a filler in the specified relation.
    These choices are data, not globally registered model instances. *)

Program Definition WitnessHornFillers (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers WitnessX n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact false. Defined.

Fail Definition unchosen_horn
  : HasHornFillers WitnessX 4 fin_first⁺⁺
  := _.

Local Instance comparison_two
  : HasHornFillers WitnessX 4 fin_first⁺⁺
  := WitnessHornFillers 4 fin_first⁺⁺ false.

Local Instance transport_three
  : HasHornFillers WitnessX 4 fin_first⁺⁺⁺
  := WitnessHornFillers 4 fin_first⁺⁺⁺ false.

Local Instance transport_four
  : HasHornFillers WitnessX 4 fin_first⁺⁺⁺⁺
  := WitnessHornFillers 4 fin_first⁺⁺⁺⁺ true.

Definition false_product
  : HasHornFillers WitnessX 3 fin_first⁺⁺
  := WitnessHornFillers 3 fin_first⁺⁺ false.

Definition true_product
  : HasHornFillers WitnessX 3 fin_first⁺⁺
  := WitnessHornFillers 3 fin_first⁺⁺ true.

Definition false_left
  : HasHornFillers WitnessX 3 fin_first⁺⁺⁺
  := WitnessHornFillers 3 fin_first⁺⁺⁺ false.

Definition true_left
  : HasHornFillers WitnessX 3 fin_first⁺⁺⁺
  := WitnessHornFillers 3 fin_first⁺⁺⁺ true.

Definition true_right
  : HasHornFillers WitnessX 3 fin_first⁺
  := WitnessHornFillers 3 fin_first⁺ true.

(** The existing hierarchy still needs explicit selection. *)

Fail Definition unchosen_group
  : HasMagma (TwoSphereClassS WitnessX true)
  := _.

Definition witness_group (b : WitnessX 0)
  : Group
  := TwoSphereClassGroup WitnessX b false_product false_left true_right.

Fail Definition unchosen_group_after_definition
  : HasMagma (TwoSphereClassS WitnessX true)
  := _.

Definition sphere_at_false
  : TwoSphereClassS WitnessX false
  := (true; λ i, false).

Definition sphere_at_true
  : TwoSphereClassS WitnessX true
  := (false; λ i, true).

Definition base_equality
  : (false : WitnessX 0) ≈S true
  := false.

(** Both sides differ as native values; the new laws compare their classes. *)

Example mapped_operations_compute
  : ((two_sphere_class_map_resp FlipN false
        (two_sphere_kan_mul WitnessX false false_product
          sphere_at_false sphere_at_false)).1,
     (two_sphere_kan_mul WitnessX true false_product
        (two_sphere_class_map_resp FlipN false sphere_at_false)
        (two_sphere_class_map_resp FlipN false sphere_at_false)).1,
     (two_sphere_class_map_resp FlipN false
        (@SphereKanLeftInverse WitnessX false false_left sphere_at_false).1).1,
     (@inv _ _ _ (hasInverse (witness_group true))
        (two_sphere_class_map_resp FlipN false sphere_at_false)).1)
      = (true, false, true, false).
Proof. vm_compute. reflexivity. Defined.

Example transported_operations_compute
  : ((two_sphere_class_change_base_resp WitnessX base_equality
        (two_sphere_kan_mul WitnessX false false_product
          sphere_at_false sphere_at_false)).1,
     (two_sphere_kan_mul WitnessX true true_product
        (two_sphere_class_change_base_resp WitnessX base_equality
          sphere_at_false)
        (two_sphere_class_change_base_resp WitnessX base_equality
          sphere_at_false)).1,
     (two_sphere_class_change_base_resp WitnessX base_equality
        (@SphereKanLeftInverse WitnessX false true_left sphere_at_false).1).1,
     (@inv _ _ _ (hasInverse (witness_group true))
        (two_sphere_class_change_base_resp WitnessX base_equality
          sphere_at_false)).1,
     (two_sphere_class_change_base_resp WitnessX base_equality
        (two_sphere_base WitnessX false)).1,
     (two_sphere_base WitnessX true).1)
      = (false, true, true, false, false, true).
Proof. vm_compute. reflexivity. Defined.

(** These clients consume the actual comparison derivations rather than
    substituting native equations between the computed representatives. *)

Definition mapped_product
  := two_sphere_class_map_mul FlipN false false_product false_product
      sphere_at_false sphere_at_false.

Definition transported_product
  := two_sphere_class_change_base_mul WitnessX base_equality
      false_product true_product sphere_at_false sphere_at_false.

Definition transported_unit
  := two_sphere_class_change_base_unit WitnessX base_equality.

Definition mapped_inverse
  := two_sphere_class_map_left_inverse FlipN false false_left
      false_product false_left true_right sphere_at_false.

Definition transported_inverse
  := two_sphere_class_change_base_left_inverse WitnessX base_equality
      true_left false_product false_left true_right sphere_at_false.

Definition corrected_inverse_product
  := two_sphere_class_inverse_mul FlipN flip_NatIso false
      false_product false_product sphere_at_true sphere_at_true.

(** The existing inverse is exactly its actual left candidate.
    This uses the law directly on the inherited group operation. *)

Example group_inverse_natural (x : TwoSphereClassS WitnessX false)
  : two_sphere_class_map_resp FlipN false
      (@inv _ _ _ (hasInverse (witness_group false)) x) ≈S
      @inv _ _ _ (hasInverse (witness_group true))
        (two_sphere_class_map_resp FlipN false x).
Proof.
  exact (two_sphere_class_map_left_inverse FlipN false false_left
    false_product false_left true_right x).
Defined.

(** The base correction is computationally present in the existing inverse. *)

Example corrected_inverse_computes
  : ((two_sphere_class_inverse_resp FlipN flip_NatIso false
        (two_sphere_kan_mul WitnessX true false_product
          sphere_at_true sphere_at_true)).1,
     (two_sphere_kan_mul WitnessX false false_product
        (two_sphere_class_inverse_resp FlipN flip_NatIso false sphere_at_true)
        (two_sphere_class_inverse_resp FlipN flip_NatIso false sphere_at_true)).1)
      = (true, false).
Proof. vm_compute. reflexivity. Defined.

(** ** Actual Cocycle Kan Fillers

    Also preserve computations in the nontrivial Boolean coefficient
    model. Here class equality distinguishes the true and false spheres;
    the identity map retains all four actual chosen Kan products. *)

Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition bool_product
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition bool_values (a b : bool)
  : bool * bool
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)
        (two_sphere_class_map_resp IdN (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
          (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            bool_product (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
            (cocycle_two_sphere_resp (M := BoolS_Monoid) b))),
      (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
        (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
          bool_product
          (two_sphere_class_map_resp IdN (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            (cocycle_two_sphere_resp (M := BoolS_Monoid) a))
          (two_sphere_class_map_resp IdN (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            (cocycle_two_sphere_resp (M := BoolS_Monoid) b)))).

Example actual_bool_products_compute
  : (bool_values false false, bool_values false true,
     bool_values true false, bool_values true true)
      = ((false, false), (true, true), (true, true), (false, false)).
Proof. vm_compute. reflexivity. Defined.

Definition actual_bool_map_product (a b : bool)
  := two_sphere_class_map_mul IdN (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      bool_product bool_product (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) b).
