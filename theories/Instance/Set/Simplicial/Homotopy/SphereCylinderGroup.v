From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinderSetoid
  Instance.Set.Simplicial.Homotopy.SphereGroup
  Algebra.Group.Transport.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * The Same Sphere Group in the Actual-Cylinder Presentation

    A sphere representative is still a based triangle, but equality in
    [TwoSphereCylinderS] now stores an actual full relative cylinder.
    The two respectful maps from the preceding presentation chapter keep
    every representative. Their element round trips therefore let us apply
    the general algebra transport of
    %\coqref{Cats.Algebra.Group.Transport.GroupTransport}
    {%[GroupTransport]%}% to the already constructed class group.

    No new geometric proof of a group law is needed: each transported
    parent is the preceding transported structure, and the product, unit
    and inverse remain the same chosen triangle, constant triangle and
    left candidate. The laws now return actual relative cylinders. They
    need not return the original generated derivations, nor compare two
    choices of filling functions or equality witnesses.

    The generated class presentation remains primary. Cylinder-equivalence
    choices and algebra choices are supplied independently, and import
    enables no model. Commutativity for general Kan objects, identification
    with general π₂, arbitrary-path transport and weak-equivalence
    invariants remain further work. The next chapter's
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderGroupMap.two_sphere_cylinder_map_mul}
    {%[two_sphere_cylinder_map_mul]%}% compares the same selected operations
    under the existing simplicial maps, without preserving chosen fillers. *)

(** * 实际柱呈现中的同一球面群

    球面代表仍为基点三角形，但 [TwoSphereCylinderS] 的相等现在保存实际完整
    相对柱。前一呈现章节的两份保相等映射保留每个代表，其元素往返律使我们
    能将通用代数运输
    %\coqref{Cats.Algebra.Group.Transport.GroupTransport}
    {%[GroupTransport]%}% 应用于已经构造的类群。

    无须重新几何证明群律：每层运输的父结构就是前一层运输结构，乘积、单位和
    逆仍是同一选定三角形、常值三角形及左候选。定律现在返回实际相对柱，
    不要求返回原生成推导，也不比较两份填充函数选择或相等见证。

    生成类呈现仍为主呈现，柱等价选择与代数选择独立显式给出，导入不启用模型。
    一般 Kan 对象的交换性、一般 π₂ 识别、任意路径运输及弱等价不变量仍需
    后续工作。下一章的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderGroupMap.two_sphere_cylinder_map_mul}
    {%[two_sphere_cylinder_map_mul]%}% 比较原单纯映射下的同一选定运算，
    不要求保持所选填充。 *)

(** The vertical maps retain representatives; their preservation equations
    compare products in generated equality on the bottom row. The transported
    top operation respects actual relative-cylinder equality. *)

(** 竖直映射保留代表，其保持方程按底行的生成相等比较乘积；运输后的顶行运算
    保持实际相对柱相等。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereCyl}_2(X,b)^2
  \arrow[r,"\mu_{\mathrm{cyl}}"] \arrow[d,"{P\times P}"'] &
\operatorname{SphereCyl}_2(X,b) \arrow[d,"P"] \\
\operatorname{SphereClass}_2(X,b)^2
  \arrow[r,"\mu_{\mathrm{gen}}"'] & \operatorname{SphereClass}_2(X,b)
\end{tikzcd}
\end{center}%
*)

(** ** Element Recovery through the Existing Maps

    Fix independent simplex carrier/equality sizes, a basepoint and the
    two nine-choice families giving the explicit cylinder setoid. No
    multiplication, inverse or full Kan structure is needed here. *)

(** ** 经既有映射恢复元素

    固定独立单形载体／相等大小、基点及显式柱广集所需的两组九选择。此处不需要
    乘法、逆或完整 Kan 结构。 *)

Section CylinderRecovery.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** Recover the same generated-class representative. No inverse equation
    on derivations or cylinders is asserted. *)

(** 恢复同一生成类代表，不声称推导或柱见证满足逆方程。 *)

Lemma two_sphere_cylinder_class_recovery
  : (two_sphere_class_of_cylinder_resp X b KR KC ∘r
      two_sphere_cylinder_of_class_resp X b KR KC) ≈f id_resp.
Proof. intros x. reflexivity. Defined.

(** Recover the cylinder representative with an actual constant relative
    cylinder, avoiding normalization of any selected reversal/composition. *)

(** 用实际常值相对柱恢复柱代表，不归约任何选定反转／复合。 *)

Lemma two_sphere_class_cylinder_recovery
  : (two_sphere_cylinder_of_class_resp X b KR KC ∘r
      two_sphere_class_of_cylinder_resp X b KR KC) ≈f id_resp.
Proof.
  intros x. exact (TwoSphereConstantCylinder X b x x
    (@reflexivity _ (carrier_equiv (TwoSphereS X b)) _ x)).
Defined.

End CylinderRecovery.

(** ** Explicitly Transporting the Selected Parent Chain

    In addition to presentation choices, fix exactly the three four-horn
    selections used by the existing class algebra. Product and inverse
    choices are independent explicit inputs to each construction. The
    comparison maps require no common upward lift of the equality sizes. *)

(** ** 显式运输选定父链

    除呈现选择外，固定既有类代数使用的三个四维 horn 选择。乘法及逆选择是各
    构造独立的显式输入，比较映射不要求将两种相等大小共同向上提升。 *)

Section CylinderAlgebra.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.

Let C
  : SetC
  := TwoSphereCylinderS X b KR KC.

(** Transport only the existing selected multiplication and its Proper
    field; it computes to the original Kan-composite representative. *)

(** 只运输既有选定乘法及其 Proper 字段，计算结果是原 Kan 合成代表。 *)

Definition TwoSphereCylinderMagma (H : HasHornFillers X 3 fin_first⁺⁺)
  : Magma C
  := MagmaTransport (two_sphere_class_of_cylinder_resp X b KR KC)
      (two_sphere_cylinder_of_class_resp X b KR KC)
      (TwoSphereClassMagma X b H).

(** General transport supplies associativity on that exact magma. *)

(** 通用运输为完全相同的原群提供结合律。 *)

Definition TwoSphereCylinderSemigroup (H : HasHornFillers X 3 fin_first⁺⁺)
  : Semigroup C
  := SemigroupTransport (two_sphere_class_of_cylinder_resp X b KR KC)
      (two_sphere_cylinder_of_class_resp X b KR KC)
      (TwoSphereClassSemigroup X b H)
      (two_sphere_cylinder_class_recovery X b KR KC).

(** Keep that semigroup and the actual constant sphere as unit. The second
    element-recovery equation supplies its two actual-cylinder unit laws. *)

(** 保留该半群，以实际常值球面为单位；第二个元素恢复方程给出两个实际柱单位律。 *)

Definition TwoSphereCylinderMonoid (H : HasHornFillers X 3 fin_first⁺⁺)
  : Monoid C
  := MonoidTransport (two_sphere_class_of_cylinder_resp X b KR KC)
      (two_sphere_cylinder_of_class_resp X b KR KC)
      (TwoSphereClassMonoid X b H)
      (two_sphere_cylinder_class_recovery X b KR KC)
      (two_sphere_class_cylinder_recovery X b KR KC).

(** Transport the existing class group, choosing its very same actual left
    candidate as inverse. Generic group inverse theory applies unchanged. *)

(** 运输既有类群，以完全相同的实际左候选为逆；通用群逆理论原样适用。 *)

Definition TwoSphereCylinderGroup
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : Group C
  := GroupTransport (two_sphere_class_of_cylinder_resp X b KR KC)
      (two_sphere_cylinder_of_class_resp X b KR KC)
      (TwoSphereClassGroup X b H K L)
      (two_sphere_cylinder_class_recovery X b KR KC)
      (two_sphere_class_cylinder_recovery X b KR KC).

(** The original comparison back to generated classes preserves this
    exact multiplication, by the generic transport equation. *)

(** 返回生成类的原比较映射保持此同一乘法，直接使用通用运输方程。 *)

Lemma two_sphere_cylinder_class_mul (H : HasHornFillers X 3 fin_first⁺⁺)
    (x y : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@magma_mul C (TwoSphereCylinderMagma H) x y) ≈S
      two_sphere_kan_mul X b H
        (two_sphere_class_of_cylinder_resp X b KR KC x)
        (two_sphere_class_of_cylinder_resp X b KR KC y).
Proof.
  exact (magma_transport_map_mul _ _ (TwoSphereClassMagma X b H)
    (two_sphere_cylinder_class_recovery X b KR KC) x y).
Defined.

(** Unit comparison uses the exact transported monoid and source unit. *)

(** 单位比较使用完全相同的运输幺半群及来源单位。 *)

Lemma two_sphere_cylinder_class_unit (H : HasHornFillers X 3 fin_first⁺⁺)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@monoid_unit C (TwoSphereCylinderMonoid H)) ≈S two_sphere_base X b.
Proof.
  exact (monoid_transport_map_unit _ _ (TwoSphereClassMonoid X b H)
    (two_sphere_cylinder_class_recovery X b KR KC)
    (two_sphere_class_cylinder_recovery X b KR KC)).
Defined.

(** Inverse comparison keeps the exact supplied product and both candidate
    selections; it does not compare selected equality witnesses. *)

(** 逆比较保留给定同一乘法及两份候选选择，不比较选定相等见证。 *)

Lemma two_sphere_cylinder_class_inv
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@group_inv C (TwoSphereCylinderGroup H K L) x) ≈S
      @group_inv _ (TwoSphereClassGroup X b H K L)
        (two_sphere_class_of_cylinder_resp X b KR KC x).
Proof.
  exact (group_transport_map_inv _ _ (TwoSphereClassGroup X b H K L)
    (two_sphere_cylinder_class_recovery X b KR KC)
    (two_sphere_class_cylinder_recovery X b KR KC) x).
Defined.

End CylinderAlgebra.
