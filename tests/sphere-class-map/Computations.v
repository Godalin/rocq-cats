From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMap
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.

(** * Distinct Representations and Retained Equality Witnesses

    This constant simplicial setoid has Boolean representations and a
    Boolean-valued equality between every pair. Both false and true are
    equality witnesses; the tests must not identify either their native
    representations or their witnesses. *)

(** * 不同表示与保留相等见证

    此常值单纯广集具有布尔表示，每对表示之间的相等也取布尔值。假与真都是
    相等见证；检查不得识别其原生表示或见证。 *)

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

(** A retained true triangle based at false. Its boundary equalities are data. *)

(** 基点为假的保留真三角形；其边界相等均为数据。 *)

Definition witness_sphere
  : TwoSphereClassS WitnessX false
  := (true; λ i, false).

(** Different specified-equality witnesses retain the exact same triangle. *)

(** 不同指定相等见证保留完全相同的三角形。 *)

Example base_change_computes
  : ((two_sphere_class_change_base_resp WitnessX
        (false : (false : WitnessX 0) ≈S true) witness_sphere).1,
     (two_sphere_class_change_base_resp WitnessX
        (true : (false : WitnessX 0) ≈S true) witness_sphere).1)
      = (true, true).
Proof. reflexivity. Defined.

(** Negation respects this specified relation without identifying Boolean data. *)

(** 取反保持此指定关系，不识别布尔数据。 *)

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

(** The forward class map changes the triangle, and its corrected inverse
    computes back to the original representation at the original base. *)

(** 正向类映射更换三角形，校正后的逆在原基点处计算回原表示。 *)

Example class_inverse_computes
  : ((two_sphere_class_map_resp FlipN false witness_sphere).1,
     (two_sphere_class_inverse_resp FlipN flip_NatIso false
       (two_sphere_class_map_resp FlipN false witness_sphere)).1)
      = (false, true).
Proof. reflexivity. Defined.

(** Consume the witness-independent coherence on the two distinct witnesses. *)

(** 在两份不同见证上消费见证无关的相干律。 *)

Definition witness_coherence
  : two_sphere_class_change_base_resp WitnessX
      (false : (false : WitnessX 0) ≈S true) witness_sphere ≈S
    two_sphere_class_change_base_resp WitnessX
      (true : (false : WitnessX 0) ≈S true) witness_sphere
  := two_sphere_class_change_base_witness WitnessX false true witness_sphere.

(** An actual tetrahedron may have a different native representation from
    its faces, since its equations use the specified Boolean relation. *)

(** 实际四面体的原生表示可以与其面不同，因为方程使用指定布尔关系。 *)

Definition witness_composite
  : TwoSphereComposite WitnessX false
      witness_sphere witness_sphere witness_sphere
  := (false; (false, (false, (false, false)))).

(** Base transport keeps the tetrahedron; mapping applies the actual
    degree-three component, which negates it in this example. *)

(** 基点运输保留四面体；映射施加实际三维分量，在此例中将其取反。 *)

Example composite_data_compute
  : ((two_sphere_composite_change_base WitnessX
        (true : (false : WitnessX 0) ≈S true) witness_composite).1,
     (two_sphere_composite_map FlipN false witness_composite).1)
      = (false, true).
Proof. reflexivity. Defined.

(** Retain a genuine elementary generator between different native triangles. *)

(** 保留不同原生三角形之间的一份真正初等生成元。 *)

Definition witness_homotopy
  : TwoSphereHomotopy WitnessX false witness_sphere
      (two_sphere_base WitnessX false)
  := (false; (true, (true, (false, false)))).

(** The class map consumes that tetrahedron derivation through its Proper
    field; it does not substitute native equality or compare proof fields. *)

(** 类映射经其 Proper 字段消费该四面体推导，不以原生相等替代，也不比较证明
    字段。 *)

Definition mapped_generator
  : two_sphere_class_map_resp FlipN false witness_sphere ≈S
      two_sphere_class_map_resp FlipN false (two_sphere_base WitnessX false)
  := @func_proper _ _ (two_sphere_class_map_resp FlipN false) _ _
      (two_sphere_class_step WitnessX false witness_homotopy).
