From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderClass
  Instance.Bool.CocycleSphereGroup
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Cylinder Descent in the Boolean Cocycle Model

    Preserve the actual two diagonal triangles and three prism tetrahedra
    from a constant relative cylinder. Inspect both comparison fillers,
    rather than replacing their chosen data by coefficient operations. *)

(** * 布尔 Cocycle 模型中的实际柱下降

    保留常值相对柱的两个实际对角三角形及三个棱柱四面体。检查两份比较填充，
    不将其选定数据替换为系数运算。 *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition actual_cylinder
  : TwoSphereCylinderHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      bool_cocycle_sphere bool_cocycle_sphere.
Proof.
  apply TwoSphereConstantCylinder.
  change (bool_cocycle_sphere.1 ≈S bool_cocycle_sphere.1). reflexivity.
Defined.

Definition diagonal (i : Ordinal 1)
  := TwoSphereCylinderDiagonal BoolCocycleModel (two_cocycle_simplex_unit 0)
      actual_cylinder i.

Definition first_low
  := SphereCylinderFirstLowHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0) actual_cylinder.

Definition middle_composite
  := SphereCylinderMiddleComposite BoolCocycleModel
      (two_cocycle_simplex_unit 0) actual_cylinder.

Definition last_homotopy
  := SphereCylinderLastHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0) actual_cylinder.

Definition converted_first
  := SphereLowHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0) first_low.

Definition middle_comparison
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0)
      (SphereLeftUnitComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
        (diagonal fin_first⁺)) middle_composite.

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example actual_prisms_compute
  : (two_cocycle_triangle_value_resp (diagonal fin_first).1,
     two_cocycle_triangle_value_resp (diagonal fin_first⁺).1,
     face_values first_low.1, face_values middle_composite.1,
     face_values last_homotopy.1)
      = (true, true, (true, true, false, false),
         (false, true, true, false), (false, false, true, true)).
Proof. vm_compute. reflexivity. Defined.

Example comparisons_compute
  : (face_values converted_first.1, face_values middle_comparison.1)
      = ((false, false, true, true), (false, false, true, true)).
Proof. vm_compute. reflexivity. Defined.

(** Descent can be consumed by the already defined coefficient invariant. *)

(** 已有系数不变量可以消费下降结果。 *)

Definition actual_class_chain
  : bool_cocycle_sphere ≈S bool_cocycle_sphere
  := two_sphere_cylinder_class BoolCocycleModel (two_cocycle_simplex_unit 0)
      actual_cylinder.

Definition decoded_class_chain
  := @func_proper _ _ cocycle_two_sphere_class_value_resp _ _
      actual_class_chain.

(** The generic theorem alone transfers the existing non-null class result
    to exclusion of a full relative cylinder. No model-specific cylinder
    classification is used in this client. *)

(** 仅用通用定理，将既有非零类结论转为排除完整相对柱；此客户端不使用模型
    特定的柱分类。 *)

Example no_relative_contraction
  : ¬ TwoSphereCylinderHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      bool_cocycle_sphere
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)).
Proof.
  intros H. exact (bool_cocycle_sphere_not_null
    (two_sphere_cylinder_class BoolCocycleModel
      (two_cocycle_simplex_unit 0) H)).
Defined.

(** ** A Nonconstant Time Map with Boolean-Valued Equality

    Time changes the actual triangle value. Endpoints have distinct native
    representations; their specified equality retains Boolean witnesses.
    Only the two required four-horn choices will be enabled. *)

(** ** 布尔值相等下的非恒定时间映射

    时间实际更换三角形的值；端点具有不同原生表示，指定相等保留布尔见证。
    只启用所需两项四维 horn 选择。 *)

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

(** Sample the second position whenever it is present. No compatibility
    with restriction is claimed in native equality; naturality below uses
    exactly the specified target relation. *)

(** 若存在第二个位置则取该位置。不声称取样与限制按原生相等相容；下方自然性
    准确使用指定目标关系。 *)

Definition sample_position (n : nat)
  : Ordinal n
  := match n with
  | 0 => fin_first
  | S k => fin_first⁺
  end.

Program Definition TimeN
  : SimplicialCylinderF (Δ[2]) ⇒ WitnessX
  :=
  {|nt n :=
      {|func z := Nat.eqb (fin_rank (lower (snd z) (sample_position n))) 0
      |}
  |}.
Next Obligation. intros z z' E. exact true. Defined.
Next Obligation. intros z. exact false. Defined.

Definition initial_sphere
  : TwoSphereS WitnessX false
  := (true; λ i, false).

Definition final_sphere
  : TwoSphereS WitnessX false
  := (false; λ i, true).

Program Definition actual_time_homotopy
  : SimplicialHomotopy (⟦initial_sphere.1⟧Δ[WitnessX; 2])
      (⟦final_sphere.1⟧Δ[WitnessX; 2])
  :=
  {|homotopy_map := TimeN
  |}.
Next Obligation. intros n z. exact true. Defined.

Definition changing_cylinder
  : TwoSphereCylinderHomotopy WitnessX false initial_sphere final_sphere.
Proof.
  exists actual_time_homotopy. intros n a t. exact false.
Defined.

(** Each choice retains an actual filler and its full horn equation. *)

(** 每份选择保留实际填充及其完整 horn 方程。 *)

Program Definition WitnessHornFillers (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers WitnessX n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact true. Defined.

Fail Definition unchosen_first_comparison
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

Fail Definition unchosen_class_group
  : Group (TwoSphereClassS WitnessX false)
  := _.

(** The time-dependent diagonal values remain visible through the subset. *)

(** 随时间变化的对角值经子集仍保持可见。 *)

Example changing_cylinder_computes
  : (initial_sphere.1,
     (TwoSphereCylinderDiagonal WitnessX false changing_cylinder
        fin_first).1,
     (TwoSphereCylinderDiagonal WitnessX false changing_cylinder
        fin_first⁺).1, final_sphere.1,
     (SphereCylinderFirstLowHomotopy WitnessX false changing_cylinder).1,
     (SphereCylinderMiddleComposite WitnessX false changing_cylinder).1,
     (SphereCylinderLastHomotopy WitnessX false changing_cylinder).1)
      = (true, true, false, false, false, true, true).
Proof. vm_compute. reflexivity. Defined.

(** The new chain connects distinct native endpoint representatives using
    the actual full relative cylinder and both comparison choices. *)

(** 新链使用实际完整相对柱及两份比较选择，连接不同原生端点表示。 *)

Definition different_representatives_class
  : (initial_sphere : TwoSphereClassS WitnessX false) ≈S final_sphere
  := two_sphere_cylinder_class WitnessX false changing_cylinder.

Definition changed_first
  := SphereLowHomotopy WitnessX false
      (SphereCylinderFirstLowHomotopy WitnessX false changing_cylinder).

Definition changed_middle
  := SphereCompositeOutputHomotopy WitnessX false
      (SphereLeftUnitComposite WitnessX false
        (TwoSphereCylinderDiagonal WitnessX false changing_cylinder
          fin_first⁺))
      (SphereCylinderMiddleComposite WitnessX false changing_cylinder).

Example independent_comparisons_compute
  : (changed_first.1, changed_middle.1) = (true, false).
Proof. vm_compute. reflexivity. Defined.

(** Count only retained elementary generators in this concrete generated
    derivation. The whole cylinder uses all three steps, not a shortcut
    through the native endpoint relation. *)

(** 只数这份具体生成推导中保留的初等生成元。完整柱使用全部三个步骤，不沿
    端点原生关系取捷径。 *)

Fixpoint elementary_steps {x y : TwoSphereS WitnessX false}
    (E : (x : TwoSphereClassS WitnessX false) ≈S y)
  : nat
  := match E with
  | closure_refl _ => 0
  | closure_step (inl _) => 0
  | closure_step (inr _) => 1
  | closure_sym F => elementary_steps F
  | closure_trans F G => elementary_steps F + elementary_steps G
  end.

Example whole_chain_computes
  : elementary_steps different_representatives_class = 3.
Proof. vm_compute. reflexivity. Defined.
