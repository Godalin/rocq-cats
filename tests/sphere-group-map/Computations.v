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

(** * 映射无需保持选定填充

    此常值单纯广集的每个相等都具有布尔见证。取反更换原生表示，选择可以独立
    返回假或真。因此交换方块必须使用生成相等，不能使用原生相等或相同选择。 *)

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

(** Retain its actual inverse map; inverse laws use the Boolean relation. *)

(** 保留其实际逆映射；互逆定律使用布尔关系。 *)

Definition flip_NatIso
  : FlipN ⦂ WitnessX ≅N WitnessX.
Proof. intros n. exists flip_resp. split; intros x; exact true. Defined.

(** Every prescribed Boolean is a filler in the specified relation.
    These choices are data, not globally registered model instances. *)

(** 按指定关系，每个给定布尔值都是填充。这些选择是数据，不全局注册模型实例。 *)

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

(** 既有层级仍须显式选择。 *)

Fail Definition unchosen_group
  : Group (TwoSphereClassS WitnessX true)
  := _.

Definition witness_group (b : WitnessX 0)
  : Group (TwoSphereClassS WitnessX b)
  := TwoSphereClassGroup WitnessX b false_product false_left true_right.

Fail Definition unchosen_group_after_definition
  : Group (TwoSphereClassS WitnessX true)
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

(** 两侧具有不同原生值；新定律比较其类。 *)

Example mapped_operations_compute
  : ((two_sphere_class_map_resp FlipN false
        (two_sphere_kan_mul WitnessX false false_product
          sphere_at_false sphere_at_false)).1,
     (two_sphere_kan_mul WitnessX true false_product
        (two_sphere_class_map_resp FlipN false sphere_at_false)
        (two_sphere_class_map_resp FlipN false sphere_at_false)).1,
     (two_sphere_class_map_resp FlipN false
        (@SphereKanLeftInverse WitnessX false false_left sphere_at_false).1).1,
     (@group_inv _ (witness_group true)
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
     (@group_inv _ (witness_group true)
        (two_sphere_class_change_base_resp WitnessX base_equality
          sphere_at_false)).1,
     (two_sphere_class_change_base_resp WitnessX base_equality
        (two_sphere_base WitnessX false)).1,
     (two_sphere_base WitnessX true).1)
      = (false, true, true, false, false, true).
Proof. vm_compute. reflexivity. Defined.

(** These clients consume the actual comparison derivations rather than
    substituting native equations between the computed representatives. *)

(** 这些客户端消费实际比较推导，不以计算后代表之间的原生方程替代。 *)

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

(** The existing group inverse is exactly its actual left candidate.
    This uses the law directly on the inherited group operation. *)

(** 既有群逆就是其实际左候选；直接在继承群运算上消费定律。 *)

Example group_inverse_natural (x : TwoSphereClassS WitnessX false)
  : two_sphere_class_map_resp FlipN false
      (@group_inv _ (witness_group false) x) ≈S
      @group_inv _ (witness_group true)
        (two_sphere_class_map_resp FlipN false x).
Proof.
  exact (two_sphere_class_map_left_inverse FlipN false false_left
    false_product false_left true_right x).
Defined.

(** The base correction is computationally present in the existing inverse. *)

(** 既有逆中实际保留可计算的基点校正。 *)

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

(** ** 实际 Cocycle Kan 填充

    同时保留非平凡布尔系数模型中的计算。在此类相等区分真、假球面；恒等映射
    保留全部四个实际选定 Kan 乘积。 *)

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition bool_product
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition bool_values (a b : bool)
  : bool * bool
  := (cocycle_two_sphere_class_value_resp
        (two_sphere_class_map_resp idN (two_cocycle_simplex_unit 0)
          (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit 0)
            bool_product (cocycle_two_sphere_resp a)
            (cocycle_two_sphere_resp b))),
      cocycle_two_sphere_class_value_resp
        (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit 0)
          bool_product
          (two_sphere_class_map_resp idN (two_cocycle_simplex_unit 0)
            (cocycle_two_sphere_resp a))
          (two_sphere_class_map_resp idN (two_cocycle_simplex_unit 0)
            (cocycle_two_sphere_resp b)))).

Example actual_bool_products_compute
  : (bool_values false false, bool_values false true,
     bool_values true false, bool_values true true)
      = ((false, false), (true, true), (true, true), (false, false)).
Proof. vm_compute. reflexivity. Defined.

Definition actual_bool_map_product (a b : bool)
  := two_sphere_class_map_mul idN (two_cocycle_simplex_unit 0)
      bool_product bool_product (cocycle_two_sphere_resp a)
      (cocycle_two_sphere_resp b).
