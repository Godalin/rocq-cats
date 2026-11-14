From Cats Require Export
  Instance.Bool.CocycleSphereGroup
  Instance.Set.Simplicial.Cocycle.SphereCylinder.

Local Existing Instance BoolS_Monoid.

(** * The Nonzero Sphere Also Survives Relative Cylinders

    The preceding order-two group used the generated tetrahedron relation.
    The comparison now proves that even a whole triangle-cylinder homotopy,
    constant along its entire boundary, cannot contract the true sphere.
    This is a relative, based statement about actual simplicial maps.
    No conclusion about all unpointed homotopy equivalences or all 1-types
    is drawn from it. The next chapter
    %\coqref{Cats.Instance.Bool.CocycleHomotopy.bool cocycle no nerve homotopy retract}
    {%[bool_cocycle_no_nerve_homotopy_retract]%}% uses invariance under
    homotopies of maps to exclude a retraction through an ordinary nerve. *)

(** * 非零球面在相对柱下仍然保留

    前章的二阶群使用生成四面体关系。现在的比较证明：即使允许整个三角柱
    的同伦，只要在其整个边界上保持常值，也不能将真球面收缩。这是关于
    实际单纯映射的相对基点陈述，不据此断言所有非基点同伦等价或所有
    1-types 的情形。下一章
    %\coqref{Cats.Instance.Bool.CocycleHomotopy.bool cocycle no nerve homotopy retract}
    {%[bool_cocycle_no_nerve_homotopy_retract]%}% 用映射同伦下的不变性
    排除经普通 nerve 的同伦收缩。 *)

(** A relative cylinder contraction would contradict the previously proved
    nonzero generated class. *)

(** 相对柱收缩会与先前证明的非零生成类相矛盾。 *)

Lemma bool_cocycle_sphere_no_relative_cylinder
  : ¬ TwoSphereCylinderHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      bool_cocycle_sphere
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)).
Proof.
  intros H. apply bool_cocycle_sphere_not_null.
  exact (cocycle_two_sphere_cylinder_class _ _ H).
Defined.
