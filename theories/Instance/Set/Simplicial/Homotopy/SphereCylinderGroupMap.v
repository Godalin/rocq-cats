From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroup
  Instance.Set.Simplicial.Homotopy.SphereGroupMap.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Mapping the Actual-Cylinder Group Operations

    The existing [two_sphere_cylinder_map_resp] keeps the image triangle
    of the original simplicial map. The preceding chapter transported
    the class group without changing its product, unit or left-candidate
    inverse. To compare their images, reuse the generated-class equations
    from
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_map_mul}
    {%[two_sphere_class_map_mul]%}% and send their witnesses through the
    original target comparison into actual full relative cylinders.

    This proves operation preservation for the same map, not preservation
    of chosen filling functions. Presentation and algebra choices at both
    ends remain independent. Only the target comparison choices are used
    beyond the old class-map hypotheses. Laws take the original sphere
    representatives as inputs. Identity and composition likewise
    follow from the old class-map laws, without constructing new maps.

    No new group-homomorphism interface or model is selected. These are
    laws for the existing chosen algebra, not general π₂ identification,
    general Kan commutativity, arbitrary-path transport or weak-equivalence
    invariance. *)

(** * 映射实际柱群的运算

    既有 [two_sphere_cylinder_map_resp] 保留原单纯映射的像三角形。前章运输类群
    时没有改变乘积、单位或左候选逆；比较其像，只需复用生成类方程
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_map_mul}
    {%[two_sphere_class_map_mul]%}%，再用原目标比较将见证送入实际完整相对柱。

    这证明同一映射保持运算，不要求保持所选填充函数。两端的呈现及代数选择均
    保持独立；除原类映射前提外，只使用目标比较选择。定律以原球面代表为输入，
    恒等及复合也直接复用
    原类映射定律，不构造新映射。

    不新建群同态接口或选择模型。这些是既有选定代数的定律，不识别一般 π₂，
    也不证明一般 Kan 交换性、任意路径运输或弱等价不变性。 *)

(** The two paths agree in actual relative-cylinder equality in the target.
    Neither the map nor the equality witness compares the selected fillers. *)

(** 两条路径在目标的实际相对柱相等下交换；映射与相等见证都不比较选定填充。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereCyl}_2(X,b)^2
  \arrow[r,"\mu_X"] \arrow[d,"{\alpha_*\times\alpha_*}"'] &
\operatorname{SphereCyl}_2(X,b) \arrow[d,"\alpha_*"] \\
\operatorname{SphereCyl}_2(Y,\alpha_0b)^2
  \arrow[r,"\mu_Y"'] & \operatorname{SphereCyl}_2(Y,\alpha_0b)
\end{tikzcd}
\end{center}%
*)

(** ** Units, Products and Left Candidates under the Same Map

    Fix independent common ambient carrier/equality bounds and explicit
    presentation choices at each end. Algebra hypotheses are local to
    the law that needs them: no source group is needed to map a candidate,
    and no four-dimensional algebra choice is needed for the unit. *)

(** ** 同一映射下的单位、乘积与左候选

    固定独立的共同环境载体／相等界，以及两端的显式呈现选择。代数前提只在需要
    的定律中给出：映射候选无须来源群，单位也不需要四维代数选择。 *)

Section CylinderMapOperations.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} (α : X ⇒ Y) (b : X 0).
Context (KRX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The original constant sphere maps to the target constant sphere by an
    actual cylinder; this needs no selected multiplication or group. *)

(** 原常值球面经实际柱映到目标常值球面，无须选定乘法或群。 *)

Lemma two_sphere_cylinder_map_unit
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY
        (two_sphere_base X b)) (two_sphere_base Y (α 0 b)).
Proof.
  exact (@func_proper _ _
    (two_sphere_cylinder_of_class_resp Y (α 0 b) KRY KCY) _ _
    (two_sphere_class_map_base α b)).
Defined.

(** Independent source and target products compare using only the old
    target missing-face-two output comparison and the presentation maps. *)

(** 独立来源和目标乘积的比较，只使用原目标缺第二面输出比较及呈现映射。 *)

Lemma two_sphere_cylinder_map_mul
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺)
    (x y : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY
        (two_sphere_kan_mul X b H x y))
      (two_sphere_kan_mul Y (α 0 b) K
        (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY x)
        (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY y)).
Proof.
  exact (@func_proper _ _
    (two_sphere_cylinder_of_class_resp Y (α 0 b) KRY KCY) _ _
    (two_sphere_class_map_mul α b H K x y)).
Defined.

(** A source left candidate maps to the target group's selected inverse.
    This is also inverse preservation for any existing source group with
    that left choice, since its inverse is definitionally this candidate. *)

(** 来源左候选映到目标群的选定逆。对以该左选择构造的任何既有来源群，这也就是
    逆保持，因为其逆按定义就是该候选。 *)

Lemma two_sphere_cylinder_map_left_inverse
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}
    `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺)
    (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY
        (@SphereKanLeftInverse X b I x).1)
      (@inv _ _ _ (hasInverse (TwoSphereCylinderGroup Y (α 0 b) KRY KCY H K L))
        (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY x)).
Proof.
  exact (@func_proper _ _
    (two_sphere_cylinder_of_class_resp Y (α 0 b) KRY KCY) _ _
    (two_sphere_class_map_left_inverse α b I H K L x)).
Defined.

End CylinderMapOperations.

(** ** Identity with an Explicit Presentation

    Fix one presentation at independent carrier/equality bounds. Its
    original identity map acts as the identity up to an actual cylinder,
    without a selected algebra structure or equality of map records. *)

(** ** 显式呈现的恒等

    在独立载体／相等界处固定一份呈现，原恒等映射按实际柱作用为恒等；无须
    选定代数结构或映射记录相等。 *)

Section CylinderMapIdentity.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** Reuse the existing identity class equation through the same comparison. *)

(** 经同一比较复用原恒等类方程。 *)

Lemma two_sphere_cylinder_map_id (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_map_resp IdN b KR KC KR KC x) x.
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KR KC) _ _
    (two_sphere_class_map_id b x)).
Defined.

End CylinderMapIdentity.

(** ** Composition with Independently Chosen Presentations

    Fix three simplicial setoids at independent common bounds and six
    presentation families. The two maps share only the expected image
    basepoint; their fillers and preservation witnesses need not agree. *)

(** ** 独立选择呈现下的复合

    在独立共同界处固定三个单纯广集及六份呈现族。两个映射只共享应有的像基点，
    不要求填充或保相等见证一致。 *)

Section CylinderMapComposition.
Universes u p.
Context {X Y Z : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (KRX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCX : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCY : ∀ s, HasHornFillers Y
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KRZ : ∀ s, HasHornFillers Z
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KCZ : ∀ s, HasHornFillers Z
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** The composition law is an actual relative cylinder, with the same
    endpoints as the old generated-class law. *)

(** 复合律是实际相对柱，其端点与原生成类定律完全相同。 *)

Lemma two_sphere_cylinder_map_comp (α : X ⇒ Y) (β : Y ⇒ Z) (b : X 0)
    (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Z (β 0 (α 0 b))
      (two_sphere_cylinder_map_resp (β ∘Nv α) b KRX KCX KRZ KCZ x)
      (two_sphere_cylinder_map_resp β (α 0 b) KRY KCY KRZ KCZ
        (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY x)).
Proof.
  exact (@func_proper _ _
    (two_sphere_cylinder_of_class_resp Z (β 0 (α 0 b)) KRZ KCZ) _ _
    (two_sphere_class_map_comp α β b x)).
Defined.

End CylinderMapComposition.

(** Specified-equality base correction for these same operations is supplied
    next by
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderBase.two_sphere_cylinder_change_base_resp}
    {%[two_sphere_cylinder_change_base_resp]%}%. It retains the triangle and
    compares actual cylinders, without arbitrary-path transport. *)

(** 下一章的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderBase.two_sphere_cylinder_change_base_resp}
    {%[two_sphere_cylinder_change_base_resp]%}% 为同一运算提供指定相等的基点校正，
    保留三角形并按实际柱比较，不涉及任意路径运输。 *)
