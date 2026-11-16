From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroupMap.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Cylinders at Equal Base Vertices

    A specified equality [E : b ≈S c] changes the constant boundary of a
    sphere while retaining its triangle. The class construction in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereMap.two_sphere_class_change_base_resp}
    {%[two_sphere_class_change_base_resp]%}% already supplies this transport.
    Place it between the two original presentation comparisons to obtain
    a respectful map for actual full relative cylinders. Its preservation
    proof may construct a new cylinder; neither input cylinders nor filling
    functions are compared.

    Identity, composition and independence of the equality witness use the
    old class equations. Operation preservation likewise reuses
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_change_base_mul}
    {%[two_sphere_class_change_base_mul]%}% and its unit/inverse companions.
    These are laws for the same selected operations, with independent
    presentation and algebra choices at the two ends. The common-lift
    isomorphism is composed from existing isomorphisms.

    Here equality is the specified equality of the vertex setoid. It is
    not an edge or a path. Arbitrary-path base change, general Kan
    commutativity, π₂ identification and weak-equivalence invariance remain
    separate goals. *)

(** * 相等基点顶点处的实际柱

    指定相等 [E : b ≈S c] 更换球面的常值边界，保留其三角形。
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereMap.two_sphere_class_change_base_resp}
    {%[two_sphere_class_change_base_resp]%}% 已经给出类运输；将它置于原有两份
    呈现比较之间，即得实际完整相对柱的保相等映射。保相等证明可以构造新柱，
    不比较输入柱或填充函数。

    恒等、复合及相等见证无关性使用原类方程。运算保持同样复用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_change_base_mul}
    {%[two_sphere_class_change_base_mul]%}% 及其单位／逆定律。定律针对同一选定
    运算，两端呈现与代数选择独立。共同提升同构由既有同构复合得到。

    此处相等是顶点广集的指定相等，并非边或路径。任意路径换基、一般 Kan
    交换性、π₂ 识别及弱等价不变性仍是独立目标。 *)

(** The square commutes on retained triangles; its lower arrow respects
    actual-cylinder equality by the two presentation comparisons. *)

(** 此方块在保留三角形上交换；下方映射经两份呈现比较保持实际柱相等。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereClass}_2(X,b)
  \arrow[r,"E_*"] \arrow[d,"I_b"'] &
\operatorname{SphereClass}_2(X,c) \arrow[d,"I_c"] \\
\operatorname{SphereCyl}_2(X,b) \arrow[r,"E_*"'] &
\operatorname{SphereCyl}_2(X,c)
\end{tikzcd}
\end{center}%
*)

(** ** Transport between Explicit Presentations

    Fix independent ambient carrier/equality bounds and two independent
    pairs of presentation choices. The map and coherence laws need no
    selected algebra; each operation law adds only its old class premise. *)

(** ** 显式呈现之间的运输

    固定独立环境载体／相等界及两对独立呈现选择。映射与相干定律不要求选定
    代数；各运算定律只增加其原类前提。 *)

Section CylinderBaseTransport.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context (KR' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC' : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** Retain the triangle and transport only its boundary witnesses. *)

(** 保留三角形，仅运输其边界见证。 *)

Definition two_sphere_cylinder_change_base_resp {b c : X 0} (E : b ≈S c)
  : TwoSphereCylinderS X b KR KC →r TwoSphereCylinderS X c KR' KC'
  := two_sphere_cylinder_of_class_resp X c KR' KC' ∘r
      (two_sphere_class_change_base_resp X E ∘r
        two_sphere_class_of_cylinder_resp X b KR KC).

(** Different vertex-equality witnesses produce an actual cylinder
    between the transported spheres, not equality of those witnesses. *)

(** 不同顶点相等见证给出运输球面间的实际柱，不要求见证本身相等。 *)

Lemma two_sphere_cylinder_change_base_witness {b c : X 0}
    (E F : b ≈S c) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X c
      (two_sphere_cylinder_change_base_resp E x)
      (two_sphere_cylinder_change_base_resp F x).
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X c KR' KC')
    _ _ (two_sphere_class_change_base_witness X E F x)).
Defined.

(** The constant sphere transports to the new constant sphere without
    any selected multiplication or algebra comparison choice. *)

(** 常值球面运输到新的常值球面，不需要选定乘法或代数比较选择。 *)

Lemma two_sphere_cylinder_change_base_unit {b c : X 0} (E : b ≈S c)
  : TwoSphereCylinderHomotopy X c
      (two_sphere_cylinder_change_base_resp E (two_sphere_base X b))
      (two_sphere_base X c).
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X c KR' KC')
    _ _ (two_sphere_class_change_base_unit X E)).
Defined.

(** Compare independent products using only missing-face-two comparison. *)

(** 只用缺第二面比较来比较独立乘积。 *)

Lemma two_sphere_cylinder_change_base_mul
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    {b c : X 0} (E : b ≈S c)
    (H K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X c
      (two_sphere_cylinder_change_base_resp E (two_sphere_kan_mul X b H x y))
      (two_sphere_kan_mul X c K
        (two_sphere_cylinder_change_base_resp E x)
        (two_sphere_cylinder_change_base_resp E y)).
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X c KR' KC')
    _ _ (two_sphere_class_change_base_mul X E H K x y)).
Defined.

(** A source left candidate transports to the inverse of the existing
    target group. No source multiplication, right candidate or group is used. *)

(** 来源左候选运输为既有目标群的逆；不使用来源乘法、右候选或群。 *)

Lemma two_sphere_cylinder_change_base_left_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    {b c : X 0} (E : b ≈S c)
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X c
      (two_sphere_cylinder_change_base_resp E
        (@SphereKanLeftInverse X b I x).1)
      (@group_inv _ (TwoSphereCylinderGroup X c KR' KC' H K L)
        (two_sphere_cylinder_change_base_resp E x)).
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X c KR' KC')
    _ _ (two_sphere_class_change_base_left_inverse X E I H K L x)).
Defined.

(** Compose the inverse source comparison, existing equal-base class
    isomorphism and target comparison at explicit common upward bounds. *)

(** 在显式共同向上界处，复合来源比较的逆、既有相等基点类同构及目标比较。 *)

Definition two_sphere_cylinder_change_base_iso@{v q +}
    {b c : X 0} (E : b ≈S c)
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X c KR' KC')
  := iso_trans (iso_symm (two_sphere_cylinder_class_iso X b KR KC))
      (iso_trans (two_sphere_class_change_base_iso X E)
        (two_sphere_cylinder_class_iso X c KR' KC')).

End CylinderBaseTransport.

(** ** Identity and Successive Transport

    The identity uses one presentation. Composition permits three
    independent presentations and compares only the final spheres by an
    actual cylinder, without identifying the equality or filling witnesses. *)

(** ** 恒等及依次运输

    恒等使用同一呈现；复合允许三份独立呈现，只按实际柱比较最终球面，不识别
    相等或填充见证。 *)

Section CylinderBaseCoherence.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** Reflexive transport acts as the identity in actual-cylinder equality. *)

(** 自反运输在实际柱相等下作用为恒等。 *)

Lemma two_sphere_cylinder_change_base_id (b : X 0) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_change_base_resp X KR KC KR KC (reflexivity b) x)
      x.
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KR KC)
    _ _ (two_sphere_class_change_base_id X b x)).
Defined.

(** Intermediate presentation choices need not agree with either end. *)

(** 中间呈现选择无须与任一端一致。 *)

Lemma two_sphere_cylinder_change_base_comp
    (KR' : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
    (KC' : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first⁺ s))
    (KR'' : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
    (KC'' : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first⁺ s))
    {b c d : X 0} (E : b ≈S c) (F : c ≈S d) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X d
      (two_sphere_cylinder_change_base_resp X KR' KC' KR'' KC'' F
        (two_sphere_cylinder_change_base_resp X KR KC KR' KC' E x))
      (two_sphere_cylinder_change_base_resp X KR KC KR'' KC''
        (transitivity E F) x).
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X d KR'' KC'')
    _ _ (two_sphere_class_change_base_comp X E F x)).
Defined.

End CylinderBaseCoherence.

(** The next chapter uses this specified-equality transport to correct the
    inverse natural transformation in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderIso.two_sphere_cylinder_inverse_resp}
    {%[two_sphere_cylinder_inverse_resp]%}%. Its round trips and operation
    laws compare actual cylinders without identifying the inverse-image base
    vertex natively. *)

(** 下一章在
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderIso.two_sphere_cylinder_inverse_resp}
    {%[two_sphere_cylinder_inverse_resp]%}% 中用此指定相等运输校正逆自然变换；
    往返及运算定律按实际柱比较，不将逆像基点顶点原生等同。 *)
