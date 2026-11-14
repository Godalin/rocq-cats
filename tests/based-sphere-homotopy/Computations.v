From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereBasedHomotopyClass
  Instance.Set.Simplicial.Homotopy.OneReduced
  Instance.Set.Terminal
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Single Constant Trajectory in Specified Equality

    The source and target below retain distinct Boolean representatives
    and Boolean equality witnesses. The homotopy actually changes a
    triangle over time, while its base trajectory is constant in the
    specified relation. No native equality of endpoints is assumed. *)

(** * 指定相等中的单条常值轨迹

    下方来源及目标保留不同布尔表示与布尔相等见证。同伦实际随时间更换三角形，
    同时基点轨迹按指定关系为常值。不预设端点的原生相等。 *)

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

(** 常值单纯对象在每一维保留这些表示。 *)

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

(** 每一维的同一个取反给出自然变换。 *)

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
          then fst z else negb (fst z)
      |}
  |}.
Next Obligation. intros z z' E. exact true. Defined.
Next Obligation. intros z. exact false. Defined.

Program Definition moving_homotopy
  : SimplicialHomotopy (idN : WitnessX ⇒ WitnessX) FlipN
  :=
  {|homotopy_map := MovingN
  |}.
Next Obligation. intros n z. exact true. Defined.

Definition false_trajectory
  : homotopy_map moving_homotopy 1
      (simplex_constant WitnessX false 1, simplex_generic 1) ≈S
      simplex_constant WitnessX true 1
  := false.

Definition true_trajectory
  : homotopy_map moving_homotopy 1
      (simplex_constant WitnessX false 1, simplex_generic 1) ≈S
      simplex_constant WitnessX true 1
  := true.

Definition source_sphere
  : TwoSphereS WitnessX false
  := (true; λ i, false).

Definition false_cylinder
  := SphereBasedHomotopyCylinder moving_homotopy false true
      false_trajectory source_sphere.

Definition true_cylinder
  := SphereBasedHomotopyCylinder moving_homotopy false true
      true_trajectory source_sphere.

(** Distinct trajectory witnesses retain the same actual cylinder map. *)

(** 不同轨迹见证保留同一实际柱映射。 *)

Example trajectory_and_endpoints_compute
  : ((idN : WitnessX ⇒ WitnessX) 0 false, FlipN 0 (false : WitnessX 0),
     homotopy_map moving_homotopy 1
       (simplex_constant WitnessX false 1, simplex_generic 1),
     simplex_constant WitnessX true 1) = (false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

Example cylinders_compute
  : (two_sphere_cylinder_eval WitnessX true false_cylinder id
       (ConstF [Ord 2] (C := [Ord 1]) fin_first),
     two_sphere_cylinder_eval WitnessX true false_cylinder id
       (ConstF [Ord 2] (C := [Ord 1]) fin_first⁺),
     two_sphere_cylinder_eval WitnessX true true_cylinder id
       (ConstF [Ord 2] (C := [Ord 1]) fin_first),
     two_sphere_cylinder_eval WitnessX true true_cylinder id
       (ConstF [Ord 2] (C := [Ord 1]) fin_first⁺))
      = (true, false, true, false).
Proof. vm_compute. reflexivity. Defined.

(** Reuse the legacy one-reduced API with its actual original endpoints. *)

(** 按其实际原端点复用旧 one-reduced 接口。 *)

Definition legacy_cylinder
  := OneReducedSphereCylinder WitnessX true (λ z, false)
      moving_homotopy false source_sphere.

Example legacy_map_computes
  : (two_sphere_cylinder_eval WitnessX true legacy_cylinder id
       (ConstF [Ord 2] (C := [Ord 1]) fin_first),
     two_sphere_cylinder_eval WitnessX true legacy_cylinder id
       (ConstF [Ord 2] (C := [Ord 1]) fin_first⁺)) = (true, false).
Proof. vm_compute. reflexivity. Defined.

(** This concrete regression checks definitional preservation of map
    values. Mathematical comparison still uses specified equality. *)

(** 此具体回归检查映射值的定义相同；数学比较仍使用指定相等。 *)

Example legacy_map_agrees (n : nat)
    (z : SimplicialCylinderF (Δ[2]) n)
  : homotopy_map legacy_cylinder.1 n z =
      homotopy_map false_cylinder.1 n z.
Proof. reflexivity. Defined.

Definition derived_initial_base
  : (false : WitnessX 0) ≈S true
  := sphere_homotopy_base moving_homotopy false true false_trajectory false.

Definition derived_final_base
  : (true : WitnessX 0) ≈S true
  := sphere_homotopy_base moving_homotopy false true false_trajectory true.

(** Only the target comparison choices are selected; no three-dimensional
    fillers or algebraic model follows from importing this theory. *)

(** 只选择目标比较；导入此理论不产生三维填充或代数模型。 *)

Program Definition WitnessHornFillers (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers WitnessX n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact true. Defined.

Fail Definition unchosen_comparison
  : HasHornFillers WitnessX 4 fin_first⁺
  := _.

Local Instance comparison_one
  : HasHornFillers WitnessX 4 fin_first⁺
  := WitnessHornFillers 4 fin_first⁺ true.

Local Instance comparison_two
  : HasHornFillers WitnessX 4 fin_first⁺⁺
  := WitnessHornFillers 4 fin_first⁺⁺ false.

Fail Definition unchosen_three
  : HasHornFillers WitnessX 3 fin_first⁺⁺
  := _.

Fail Definition unchosen_full_Kan
  : HasKanFillers WitnessX
  := _.

Definition actual_class_map_equality
  := two_sphere_class_map_homotopy moving_homotopy false true
      false_trajectory.

Definition different_image_classes
  := actual_class_map_equality source_sphere.

(** ** A Target with a Genuinely Nonconstant Edge

    The standard interval has distinct vertices, so it does not satisfy
    the one-reduced edge law. A constant homotopy still has the required
    constant trajectory, and its restricted cylinder needs no Kan data. *)

(** ** 具有真正非常值边的目标

    标准区间具有不同顶点，不满足 one-reduced 边定律。恒定同伦仍具有所需
    常值轨迹，限制柱无需 Kan 数据。 *)

Definition interval_model
  : Fct (Δ^op) SetCat
  := Δ[1].

Definition interval_base
  : interval_model 0
  := SimplicialIntervalPointN false 0 tt.

Definition constant_interval_homotopy
  : SimplicialHomotopy (idN : interval_model ⇒ interval_model) idN
  := SimplicialConstantHomotopy idN.

Definition constant_interval_trace
  : homotopy_map constant_interval_homotopy 1
      (simplex_constant interval_model interval_base 1, simplex_generic 1) ≈S
      simplex_constant interval_model interval_base 1.
Proof. reflexivity. Defined.

Definition interval_cylinder
  := SphereBasedHomotopyCylinder constant_interval_homotopy interval_base
      interval_base constant_interval_trace
      (two_sphere_base interval_model interval_base).

Example interval_cylinder_computes
  : fin_rank (lower (two_sphere_cylinder_eval interval_model interval_base
      interval_cylinder id σ[1; fin_first]) fin_first⁺⁺) = 0.
Proof. vm_compute. reflexivity. Defined.

(** The moving point homotopy supplies the generic interval edge. Its
    terminal endpoint differs from that of the proposed constant edge;
    the explicit trajectory hypothesis therefore cannot be omitted. *)

(** 移动点同伦提供区间的泛边，其终止端点不同于所提常值边的终点。因此不能
    省略显式轨迹假设。 *)

Example moving_point_trace_not_constant
  : ¬ (homotopy_map SimplicialPointHomotopy 1
      (simplex_constant (ConstF (Δ^op) UnitS) tt 1, simplex_generic 1) ≈S
      simplex_constant interval_model interval_base 1).
Proof.
  intros [E].
  pose proof (fst (simplex_eq_iff _ _) E fin_first⁺) as F.
  change ((fin_first⁺ : Ordinal 1) = fin_first) in F. discriminate F.
Defined.
