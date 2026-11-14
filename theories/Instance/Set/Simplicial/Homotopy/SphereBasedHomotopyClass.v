From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereBasedHomotopy
  Instance.Set.Simplicial.Homotopy.SphereCylinderClass.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Constant-Trajectory Homotopies Agree on Sphere Classes

    The preceding construction retained an actual relative cylinder for
    each source sphere. Apply
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderClass.two_sphere_cylinder_class}
    {%[two_sphere_cylinder_class]%}% in the target. This compares the
    existing class maps after their explicit derived base corrections;
    it neither creates a new map interface nor identifies natural
    transformations or functions in native equality. *)

(** * 常值轨迹同伦在球面类上作用一致

    前面的构造为每个源球面保留实际相对柱。现于目标应用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderClass.two_sphere_cylinder_class}
    {%[two_sphere_cylinder_class]%}%，比较既有类映射经显式导出的基点校正
    后的结果。不新建映射接口，也不按原生相等识别自然变换或函数。 *)

(** ** Only Target Comparison Choices

    Keep independent ambient sizes and an arbitrary source. Only the
    target has dimension-four missing-face-one/two choices. The explicit
    constant trajectory remains essential; no arbitrary path transport,
    general π₂ identification or weak-equivalence invariance is claimed. *)

(** ** 仅需目标比较选择

    保留独立环境大小及任意来源，只有目标具有四维缺第一／第二面选择。显式
    常值轨迹仍是必要条件；不声称任意路径换基、一般 π₂ 或弱等价不变量。 *)

Section BasedHomotopyClassMaps.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Y}.
Context `{HY1 : !HasHornFillers Y 4 fin_first⁺}.
Context `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}.

(** The same respectful class maps agree pointwise after base correction. *)

(** 同样的保相等类映射经基点校正后逐点一致。 *)

Lemma two_sphere_class_map_homotopy (H : SimplicialHomotopy f g)
    (b : X 0) (c : Y 0)
    (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
      ≈S simplex_constant Y c 1)
  : (two_sphere_class_change_base_resp Y (sphere_homotopy_base H b c E false)
      ∘r two_sphere_class_map_resp f b) ≈f
      (two_sphere_class_change_base_resp Y (sphere_homotopy_base H b c E true)
        ∘r two_sphere_class_map_resp g b).
Proof.
  intros x. exact (two_sphere_cylinder_class Y c
    (SphereBasedHomotopyCylinder H b c E x)).
Defined.

End BasedHomotopyClassMaps.
