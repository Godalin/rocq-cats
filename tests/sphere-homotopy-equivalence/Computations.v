From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereHomotopyEquivalence
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Homotopy Inverses Need Not Be Native Inverses

    Negation and identity are not native inverses on Boolean carriers.
    With Boolean-valued specified equality, the actual time-varying
    homotopy below contracts their composites. Its two base trajectories
    and the resulting correction witnesses remain distinct data. *)

(** * 实际同伦逆无需原生互逆

    在布尔载体上取反与恒等并不原生互逆。在布尔值指定相等中，下方实际随时间
    变化的同伦收缩其复合；两个基点轨迹及所得校正见证仍为不同数据。 *)

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

Definition WitnessX
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Program Definition flip_resp
  : WitnessS →r WitnessS
  :=
  {|func := negb
  |}.
Next Obligation. intros x y E. exact E. Defined.

Program Definition FlipN
  : WitnessX ⇒ WitnessX
  :=
  {|nt n := flip_resp
  |}.
Next Obligation. intros x. exact true. Defined.

Program Definition MovingN
  : SimplicialCylinderF WitnessX ⇒ WitnessX
  :=
  {|nt n :=
      {|func z := if Nat.eqb (fin_rank (lower (snd z) fin_first)) 0
          then negb (fst z) else fst z
      |}
  |}.
Next Obligation. intros z z' E. exact true. Defined.
Next Obligation. intros z. exact false. Defined.

Program Definition left_homotopy
  : SimplicialHomotopy ((IdN : WitnessX ⇒ WitnessX) ∘Nv FlipN) IdN
  :=
  {|homotopy_map := MovingN
  |}.
Next Obligation. intros n z. exact true. Defined.

Program Definition right_homotopy
  : SimplicialHomotopy (FlipN ∘Nv (IdN : WitnessX ⇒ WitnessX)) IdN
  :=
  {|homotopy_map := MovingN
  |}.
Next Obligation. intros n z. exact false. Defined.

Definition left_trajectory
  : homotopy_map left_homotopy 1
      (simplex_constant WitnessX false 1, simplex_generic 1) ≈S
      simplex_constant WitnessX false 1
  := false.

Definition right_trajectory
  : homotopy_map right_homotopy 1
      (simplex_constant WitnessX (FlipN 0 false) 1, simplex_generic 1) ≈S
      simplex_constant WitnessX (FlipN 0 false) 1
  := true.

(** No comparison structure is selected by import or by defining the maps. *)

(** 导入或定义映射都不选择比较结构。 *)

Fail Definition unchosen_comparison
  : HasHornFillers WitnessX 4 fin_first⁺
  := _.

Definition reverse_resp
  := two_sphere_class_homotopy_inverse_resp FlipN IdN false
      left_homotopy left_trajectory.

Definition source_sphere
  : TwoSphereClassS WitnessX false
  := (true; λ i, false).

Definition target_sphere
  : TwoSphereClassS WitnessX (FlipN 0 false)
  := (false; λ i, true).

Example actual_roundtrip_values
  : (source_sphere.1,
     (reverse_resp (two_sphere_class_map_resp FlipN false source_sphere)).1,
     target_sphere.1,
     (two_sphere_class_map_resp FlipN false (reverse_resp target_sphere)).1)
      = (true, false, false, true).
Proof. vm_compute. reflexivity. Defined.

Example actual_trajectories_and_correction_compute
  : (homotopy_map left_homotopy 1
       (simplex_constant WitnessX false 1, simplex_generic 1),
     homotopy_map right_homotopy 1
       (simplex_constant WitnessX true 1, simplex_generic 1),
     sphere_homotopy_base left_homotopy false false left_trajectory false,
     sphere_homotopy_base right_homotopy true true right_trajectory false)
      = (true, false, true, false).
Proof. vm_compute. reflexivity. Defined.

Program Definition WitnessHornFillers (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers WitnessX n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact true. Defined.

Local Instance comparison_one
  : HasHornFillers WitnessX 4 fin_first⁺
  := WitnessHornFillers 4 fin_first⁺ true.

Local Instance comparison_two
  : HasHornFillers WitnessX 4 fin_first⁺⁺
  := WitnessHornFillers 4 fin_first⁺⁺ false.

Fail Definition unchosen_three
  : HasHornFillers WitnessX 3 fin_first⁺⁺
  := _.

Fail Definition unchosen_transport_three
  : HasHornFillers WitnessX 4 fin_first⁺⁺⁺
  := _.

Fail Definition unchosen_transport_four
  : HasHornFillers WitnessX 4 fin_first⁺⁺⁺⁺
  := _.

Fail Definition unchosen_full_Kan
  : HasKanFillers WitnessX
  := _.

(** Both laws use real homotopy comparison chains despite unequal native
    roundtrip values. Reflection also consumes an actual elementary step. *)

(** 原生往返值不同，但两律消费实际同伦比较链。反映性也消费实际初等步骤。 *)

Definition witness_left
  : reverse_resp (two_sphere_class_map_resp FlipN false source_sphere)
      ≈S source_sphere
  := two_sphere_class_homotopy_inverse_l FlipN IdN false
      left_homotopy left_trajectory source_sphere.

Definition witness_right
  : two_sphere_class_map_resp FlipN false (reverse_resp target_sphere)
      ≈S target_sphere
  := two_sphere_class_homotopy_inverse_r FlipN IdN false
      left_homotopy left_trajectory right_homotopy right_trajectory
      target_sphere.

Definition another_source_sphere
  : TwoSphereClassS WitnessX false
  := (false; λ i, true).

Definition actual_image_step
  : TwoSphereHomotopy WitnessX (FlipN 0 false)
      (two_sphere_class_map_resp FlipN false source_sphere)
      (two_sphere_class_map_resp FlipN false another_source_sphere)
  := (true; (false, (true, (false, true)))).

Definition reflected_generated_step
  : source_sphere ≈S another_source_sphere
  := two_sphere_class_map_homotopy_reflect FlipN IdN false
      left_homotopy left_trajectory source_sphere another_source_sphere
      (two_sphere_class_step WitnessX (FlipN 0 false) actual_image_step).

Definition witness_iso
  := two_sphere_class_homotopy_iso FlipN IdN false
      left_homotopy left_trajectory right_homotopy right_trajectory.

Example iso_maps_compute
  : ((lower (witness_iso.1 {|lower := source_sphere|})).1,
     (lower (witness_iso.2.1 {|lower := target_sphere|})).1) = (false, false).
Proof. vm_compute. reflexivity. Defined.

(** ** A Nontrivial Actual Kan Model

    The Boolean cocycle classes remain distinct. Apply the generic
    isomorphism to actual identity homotopies, with the existing Kan
    model enabled explicitly. No class Group is needed. *)

(** ** 非平凡实际 Kan 模型

    布尔 cocycle 类仍可区分。显式启用既有 Kan 模型后，将一般同构应用于实际
    恒等同伦；无需类群结构。 *)

Local Existing Instance BoolCocycleModel_HasKanFillers.

Program Definition bool_identity_homotopy
  : SimplicialHomotopy
      ((IdN : BoolCocycleModel ⇒ BoolCocycleModel) ∘Nv IdN) IdN
  :=
  {|homotopy_map := homotopy_map
      (SimplicialConstantHomotopy (IdN : BoolCocycleModel ⇒ BoolCocycleModel))
  |}.
Next Obligation. destruct b; intros n z; reflexivity. Defined.

Definition bool_identity_trajectory
  : homotopy_map bool_identity_homotopy 1
      (simplex_constant BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) 1,
       simplex_generic 1) ≈S
      simplex_constant BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) 1.
Proof. reflexivity. Defined.

Definition bool_class_iso
  := two_sphere_class_homotopy_iso IdN IdN (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      bool_identity_homotopy bool_identity_trajectory
      bool_identity_homotopy bool_identity_trajectory.

Example nontrivial_maps_compute
  : (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)
       (lower (bool_class_iso.1 {|lower := bool_cocycle_sphere|})),
     (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
       (lower (bool_class_iso.2.1 {|lower := bool_cocycle_sphere|})))
      = (true, true).
Proof. vm_compute. reflexivity. Defined.

Definition nontrivial_left_roundtrip
  := fst bool_class_iso.2.2 {|lower := bool_cocycle_sphere|}.

Definition nontrivial_right_roundtrip
  := snd bool_class_iso.2.2 {|lower := bool_cocycle_sphere|}.

(** Equality reflection preserves the proved non-null class, independently
    of coefficient evaluation in the generic comparison proof. *)

(** 相等反映保持已证明非零的类，一般比较证明并不依赖系数求值。 *)

Example non_null_image
  : ¬ (two_sphere_class_map_resp (IdN : BoolCocycleModel ⇒ BoolCocycleModel)
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) bool_cocycle_sphere ≈S
      two_sphere_class_map_resp IdN (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
        (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0))).
Proof.
  intros F. apply bool_cocycle_sphere_not_null.
  exact (two_sphere_class_map_homotopy_reflect IdN IdN
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) bool_identity_homotopy
    bool_identity_trajectory _ _ F).
Defined.
