From Cats Require Import
  Instance.Set.Simplicial.TriangleInput
  Instance.Set.Simplicial.TriangleIteration
  Cat.Diagram.Core
  Cat.Core.
From Stdlib Require Import
  Lists.List.

Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Initial Maps without Kan Choices

    Time projection is nonconstant and is defined even for the standard
    triangle, which has not been supplied any Kan structure. A second
    model retains different native values on equal overlap points. *)

(** * 无需 Kan 选择的实际初始映射

    时间投影不是常值，即使目标为未给定 Kan 结构的标准三角形仍可定义。
    第二个模型在相等的交叠点上保留不同原生值。 *)

Program Definition boundary_time
  : SimplicialParameterF (∂Δ[2]) 2 ⇒ (Δ[2])
  :=
  {|nt n := {|func x := snd x|}
  |}.
Next Obligation. intros [a t] [a' t'] [E F]. exact F. Defined.
Next Obligation. intros x. reflexivity. Defined.

Program Definition face_time (j : Ordinal 2)
  : SimplicialCylinderF (Δ[2]) ⇒ (Δ[2])
  :=
  {|nt n := {|func x := {|lower := δ[1; j] ∘ lower (snd x)|}|}
  |}.
Next Obligation.
  intros [a t] [a' t'] [E F].
  refine {|lower := _|}.
  exact (@comp_l Δ n 1%nat 2 δ[1; j] (lower t) (lower t') (lower F)).
Defined.
Next Obligation.
  intros x. refine {|lower := _|}. symmetry.
  exact (@comp_assoc Δ Y X 1%nat 2 δ[1; j] (lower (snd x)) f).
Defined.

Definition time_boundary_agreement (r : Ordinal 2)
  : triangle_input_boundary_agreement r boundary_time face_time.
Proof. intros j Hj n a t. reflexivity. Defined.

Definition time_face_agreement (r : Ordinal 2)
  : triangle_input_face_agreement r face_time.
Proof. intros j k Hj Hk n a t t' E. exact {|lower := E|}. Defined.

Definition time_input (r : Ordinal 2)
  : TriangleHornStage r 0 ⇒ (Δ[2])
  := TriangleInputN r boundary_time face_time
      (time_boundary_agreement r) (time_face_agreement r).

Definition parameters
  : list (Ordinal 2)
  := [(fin_first : Ordinal 2); fin_first⁺; fin_first⁺⁺].

Definition space_boundary
  : (∂Δ[2]) 1%nat.
Proof.
  refine {|lower := (δ[1; fin_first]; _)|}.
  exists fin_first, (id : (@Hom Δ) 1%nat 1%nat). symmetry. apply comp_id_r.
Defined.

Definition kept_face (r : Ordinal 2)
  : ∃ j : Ordinal 2, ¬ j = r.
Proof.
  destruct r as [[] | [[] | [[] | []]]].
  - exists (fin_first⁺ : Ordinal 2). discriminate.
  - exists fin_first. discriminate.
  - exists fin_first. discriminate.
Defined.

Definition edge_ranks {m : nat} (f : (@Hom Δ) 1%nat m)
  : list nat
  := [fin_rank (f fin_first); fin_rank (f fin_first⁺)].

Definition six_ranks {m : nat} (f : (@Hom Δ) 5 m)
  : list nat
  := [fin_rank (f fin_first); fin_rank (f fin_first⁺);
      fin_rank (f fin_first⁺⁺); fin_rank (f fin_first⁺⁺⁺);
      fin_rank (f fin_first⁺⁺⁺⁺); fin_rank (f fin_first⁺⁺⁺⁺⁺)].

Example actual_boundary_time_values
  : map (λ r, edge_ranks
      (lower (time_input r 1%nat
        (triangle_input_generator r (inl (1%nat;
          (space_boundary, {|lower := δ[1; fin_first⁺]|}))))))) parameters =
      repeat ([0; 2]) 3.
Proof. vm_compute. reflexivity. Defined.

Example actual_retained_face_time_values
  : map (λ r, edge_ranks
      (lower (time_input r 1%nat
        (triangle_input_generator r (inr ((kept_face r).1;
          ((kept_face r).2, (1%nat;
            ({|lower := δ[1; fin_first]|},
             simplex_generic 1%nat))))))))) parameters =
      [[0; 2]; [1; 2]; [1; 2]].
Proof. vm_compute. reflexivity. Defined.

Definition five_factor
  : (@Hom Δ) 5 1%nat
  := σ[1; fin_first] ∘ σ[2; fin_first] ∘ σ[3; fin_first] ∘ σ[4; fin_first].

Definition five_point (r : Ordinal 2)
  : TriangleHornStage r 0 5
  := fmap (TriangleHornStage r 0) five_factor
      (triangle_input_generator r (inr ((kept_face r).1;
        ((kept_face r).2, (1%nat;
          ({|lower := δ[1; fin_first]|}, simplex_generic 1%nat)))))).

Example degenerate_face_time_values
  : map (λ r, six_ranks (lower (time_input r 5 (five_point r)))) parameters =
      [[0; 0; 0; 0; 0; 2]; [1; 1; 1; 1; 1; 2]; [1; 1; 1; 1; 1; 2]].
Proof. vm_compute. reflexivity. Defined.

Program Definition direct_time (r : Ordinal 2)
  : TriangleHornStage r 0 ⇒ (Δ[2])
  :=
  {|nt n := {|func x := snd x.1|}
  |}.
Next Obligation.
  intros [[a t] M] [[a' t'] M'] [E F]. exact F.
Defined.
Next Obligation. intros x. reflexivity. Defined.

Definition actual_time_uniqueness (r : Ordinal 2)
  : direct_time r ≈N time_input r.
Proof.
  apply triangle_input_unique.
  - intros n [a t]. reflexivity.
  - intros j Hj n [a t]. reflexivity.
Defined.

(** ** Native Values and Independent Law Witnesses

    The specified equality has Boolean witnesses and relates all values.
    Gluing must preserve that relation without imposing native equality. *)

(** ** 原生取值与独立定律见证

    指定相等具有布尔见证，关联全部取值。粘合须保持该关系，不强加原生相等。 *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation. split; red; intros; exact true. Defined.

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Program Definition boundary_value (v : bool)
  : SimplicialParameterF (∂Δ[2]) 2 ⇒ W
  :=
  {|nt n := {|func x := v|}
  |}.
Next Obligation. intros x y E. exact true. Defined.
Next Obligation. intros x. exact true. Defined.

Program Definition face_value (v : bool) (j : Ordinal 2)
  : SimplicialCylinderF (Δ[2]) ⇒ W
  :=
  {|nt n := {|func x := v|}
  |}.
Next Obligation. intros x y E. exact false. Defined.
Next Obligation. intros x. exact true. Defined.

Definition witness_boundary_agreement (r : Ordinal 2) (v : bool)
  : triangle_input_boundary_agreement r (boundary_value true) (face_value false).
Proof. intros j Hj n a t. exact v. Defined.

Definition witness_face_agreement (r : Ordinal 2) (v : bool)
  : triangle_input_face_agreement r (face_value false).
Proof. intros j k Hj Hk n a t t' E. exact v. Defined.

Definition witness_input (r : Ordinal 2) (v : bool)
  : TriangleHornStage r 0 ⇒ W
  := TriangleInputN r (boundary_value true) (face_value false)
      (witness_boundary_agreement r v) (witness_face_agreement r v).

Definition boundary_point (r : Ordinal 2)
  : TriangleHornStage r 0 1%nat
  := triangle_input_generator r (inl (1%nat;
      (space_boundary, {|lower := δ[1; (kept_face r).1]|}))).

Definition face_point (r : Ordinal 2)
  : TriangleHornStage r 0 1%nat
  := triangle_input_generator r (inr ((kept_face r).1;
      ((kept_face r).2, (1%nat;
        (ι∂[2] 1%nat space_boundary, simplex_generic 1%nat))))).

Definition overlap_points_equal (r : Ordinal 2)
  : boundary_point r ≈S face_point r.
Proof.
  split; [reflexivity |]. refine {|lower := _|}. symmetry.
  exact (@comp_id_r Δ 1%nat 2 δ[1; (kept_face r).1]).
Defined.

Example retained_overlap_values_are_not_native_equal
  : map (λ r, (witness_input r false 1%nat (boundary_point r),
                witness_input r true 1%nat (face_point r))) parameters =
      repeat (true, false) 3.
Proof. vm_compute. reflexivity. Defined.

Definition independent_witnesses (r : Ordinal 2)
  : witness_input r false ≈N witness_input r true.
Proof.
  apply triangle_input_proper.
  - intros n z. exact false.
  - intros j Hj n z. exact true.
Defined.

Definition real_overlap_respectfulness (r : Ordinal 2)
  : witness_input r false 1%nat (boundary_point r) ≈S
      witness_input r false 1%nat (face_point r)
  := @func_proper _ _ (witness_input r false 1%nat) _ _
      (overlap_points_equal r).

Fail Definition overlap_recovery_is_native (r : Ordinal 2)
  : witness_input r false 1%nat (boundary_point r) =
      witness_input r false 1%nat (face_point r)
  := ltac:(vm_compute; reflexivity).

Fail Definition automatic_kan
  : HasKanFillers W
  := ltac:(typeclasses eauto).

Fail Definition automatic_pushout
  : HasPushout (FctCat (Δ^op) SetCat)
  := ltac:(typeclasses eauto).

(** ** The Omitted Value is Unconstrained

    In native Boolean equality, all retained edges have value true while
    the omitted entry is false. Incompatible retained boundary data are
    genuinely rejected, rather than being hidden in a gluing assumption. *)

(** ** 缺失项不受约束

    对原生布尔相等，保留边全部取真而缺失项取假。不相容保留边界数据确实
    不可接受，不会藏在粘合假设中。 *)

Program Definition DiscreteS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv := eq
  ; carrier_setoid := eq_equivalence
  |}.

Definition DiscreteF
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) DiscreteS.

Program Definition constant_map (A : Fct (Δ^op) SetCat) (v : bool)
  : A ⇒ DiscreteF
  :=
  {|nt n := {|func x := v|}
  |}.
Next Obligation. intros x y E. reflexivity. Defined.
Next Obligation. intros x. reflexivity. Defined.

Definition face_dec (r j : Ordinal 2)
  : {j = r} + {j <> r}
  := ltac:(repeat decide equality).

Definition face_flag (r j : Ordinal 2)
  : bool
  := if face_dec r j
      then false else true.

Definition retained_flag (r j : Ordinal 2) (Hj : ¬ j = r)
  : face_flag r j = true.
Proof. unfold face_flag.
  destruct (face_dec r j) as [E | E]; [destruct (Hj E) | reflexivity].
Defined.

Definition discrete_boundary
  := constant_map (SimplicialParameterF (∂Δ[2]) 2) true.

Definition discrete_face (r j : Ordinal 2)
  := constant_map (SimplicialCylinderF (Δ[2])) (face_flag r j).

Definition discrete_boundary_agreement (r : Ordinal 2)
  : triangle_input_boundary_agreement r discrete_boundary (discrete_face r).
Proof. intros j Hj n a t. symmetry. exact (retained_flag r j Hj). Defined.

Definition discrete_face_agreement (r : Ordinal 2)
  : triangle_input_face_agreement r (discrete_face r).
Proof.
  intros j k Hj Hk n a t t' E.
  transitivity true; [apply retained_flag; exact Hj |].
  symmetry. apply retained_flag. exact Hk.
Defined.

Definition discrete_input (r : Ordinal 2)
  := TriangleInputN r discrete_boundary (discrete_face r)
      (discrete_boundary_agreement r) (discrete_face_agreement r).

Example omitted_value_is_not_used
  : map (λ r, (discrete_input r 1%nat (boundary_point r),
      discrete_input r 1%nat (face_point r), face_flag r r)) parameters =
      repeat (true, true, false) 3.
Proof. vm_compute. reflexivity. Defined.

Definition incompatible_boundary_data (r : Ordinal 2)
    (E : triangle_input_boundary_agreement r discrete_boundary
      (λ _, constant_map (SimplicialCylinderF (Δ[2])) false))
  : False.
Proof.
  pose proof (E (kept_face r).1 (kept_face r).2 1%nat
    space_boundary (simplex_generic 1%nat)) as F.
  discriminate F.
Defined.

Fail Definition agreement_is_not_automatic (r : Ordinal 2)
  : triangle_input_boundary_agreement r discrete_boundary
      (λ _, constant_map (SimplicialCylinderF (Δ[2])) false)
  := ltac:(intros; reflexivity).
