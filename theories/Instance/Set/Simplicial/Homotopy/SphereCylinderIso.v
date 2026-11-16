From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinderBase.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Natural Isomorphisms and Actual-Cylinder Sphere Groups

    A natural isomorphism [α] has an inverse transformation [β]. On based
    spheres, [β] first lands at [β 0 (α 0 b)], which need not be the original
    vertex [b]. Its inverse equation supplies specified vertex equality.
    Compose the existing cylinder map with
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderBase.two_sphere_cylinder_change_base_resp}
    {%[two_sphere_cylinder_change_base_resp]%}% to make that correction.

    The corrected inverse has exactly the representative of the original
    class inverse in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereMap.two_sphere_class_inverse_resp}
    {%[two_sphere_class_inverse_resp]%}%. Reuse its two round-trip equations
    and product equation through the old target presentation comparison.
    Unit and left-candidate inverse preservation compose the already proved
    map and base-change laws. Compose the latter class equations before
    constructing its cylinder, so intermediate cylinder proofs need not
    unfold at the transparent proof boundary. The common-lift isomorphism is
    likewise a composite of the existing class isomorphism and presentation
    comparisons.

    Thus both directions preserve the original selected group operations
    when those structures are explicitly supplied. No second group-hom
    interface, filler preservation or equality of inverse witnesses is used.
    Natural isomorphism is the hypothesis here; arbitrary homotopy/weak
    equivalences, arbitrary-path transport, general Kan commutativity and
    general π₂ identification remain separate work. *)

(** * 自然同构与实际柱球面群

    自然同构 [α] 具有逆变换 [β]。在基点球面上，[β] 首先落到
    [β 0 (α 0 b)]，该顶点未必就是原顶点 [b]；互逆方程提供指定顶点相等。
    将既有柱映射与
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderBase.two_sphere_cylinder_change_base_resp}
    {%[two_sphere_cylinder_change_base_resp]%}% 复合，完成此校正。

    校正逆的代表恰好是原类逆
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereMap.two_sphere_class_inverse_resp}
    {%[two_sphere_class_inverse_resp]%}% 的代表。经原目标呈现比较复用其两条
    往返方程及乘积方程。单位与左候选逆保持复合已证映射及换基定律。后者先复合
    类方程再构造柱，避免在透明证明边界展开中间柱证明；共同提升同构也复合原类
    同构与呈现比较。

    因而在显式给出原选定群结构时，两个方向均保持原运算。不新建群同态接口，
    不要求保持填充或互逆见证相等。此处前提是自然同构；任意同伦／弱等价、
    任意路径换基、一般 Kan 交换性及一般 π₂ 识别仍需独立研究。 *)

(** The corrected inverse follows the two lower arrows. Its intermediate
    vertex is retained explicitly; ε is the specified inverse equation. *)

(** 校正逆沿下方两箭头前进；中间顶点显式保留，ε为指定互逆方程。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereCyl}_2(X,b)
  \arrow[r,"\alpha_*"] \arrow[d,equal] &
\operatorname{SphereCyl}_2(Y,\alpha_0b) \arrow[d,"\beta_*"] \\
\operatorname{SphereCyl}_2(X,b) &
\operatorname{SphereCyl}_2(X,\beta_0\alpha_0b)
  \arrow[l,"\varepsilon_*"']
\end{tikzcd}
\end{center}%
*)

(** ** Corrected Inverse and Round Trips

    Fix independent ambient bounds, a natural isomorphism and the source
    basepoint. Each end supplies its independent presentation choices.
    These suffice for the inverse, round trips, unit law and common-lift
    comparison; algebra choices appear only in the operation law using them. *)

(** ** 校正逆及往返

    固定独立环境界、自然同构及来源基点。两端提供独立呈现选择，足以构造逆、
    往返、单位律及共同提升比较；代数选择只在使用它们的运算定律中出现。 *)

Section CylinderIsomorphism.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (α : X ⇒ Y) (A : α ⦂ X ≅N Y) (b : X 0).
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

(** First map by the inverse transformation, then correct its basepoint
    using the same X presentation at both X vertices. *)

(** 先沿逆变换映射，再使用两个 X 顶点处的同一 X 呈现校正基点。 *)

Definition two_sphere_cylinder_inverse_resp
  : TwoSphereCylinderS Y (α 0 b) KRY KCY →r TwoSphereCylinderS X b KRX KCX
  := two_sphere_cylinder_change_base_resp X KRX KCX KRX KCX
      (fst (A 0).2 b) ∘r
      two_sphere_cylinder_map_resp (α ^-1N A) (α 0 b) KRY KCY KRX KCX.

(** The corrected inverse recovers a source sphere by an actual cylinder. *)

(** 校正逆按实际柱恢复来源球面。 *)

Lemma two_sphere_cylinder_inverse_l (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_inverse_resp
        (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY x)) x.
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KRX KCX)
    _ _ (two_sphere_class_inverse_l α A b x)).
Defined.

(** The original forward map recovers every target sphere after correction. *)

(** 原正向映射在校正后恢复每个目标球面。 *)

Lemma two_sphere_cylinder_inverse_r (y : TwoSphereS Y (α 0 b))
  : TwoSphereCylinderHomotopy Y (α 0 b)
      (two_sphere_cylinder_map_resp α b KRX KCX KRY KCY
        (two_sphere_cylinder_inverse_resp y)) y.
Proof.
  exact (@func_proper _ _
    (two_sphere_cylinder_of_class_resp Y (α 0 b) KRY KCY)
    _ _ (two_sphere_class_inverse_r α A b y)).
Defined.

(** Map the unit by the inverse transformation before applying base
    transport. Both existing unit laws need no algebra choice. *)

(** 先沿逆变换映射单位，再作基点运输；两条既有单位律均不需代数选择。 *)

Lemma two_sphere_cylinder_inverse_unit
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_inverse_resp (two_sphere_base Y (α 0 b)))
      (two_sphere_base X b).
Proof.
  change ((two_sphere_cylinder_inverse_resp
    (two_sphere_base Y (α 0 b)) : TwoSphereCylinderS X b KRX KCX) ≈S
    two_sphere_base X b).
  transitivity (two_sphere_cylinder_change_base_resp X KRX KCX KRX KCX
    (fst (A 0).2 b) (two_sphere_base X ((α ^-1N A) 0 (α 0 b)))).
  - exact (@func_proper _ _
      (two_sphere_cylinder_change_base_resp X KRX KCX KRX KCX
        (fst (A 0).2 b)) _ _
      (two_sphere_cylinder_map_unit (α ^-1N A) (α 0 b) KRY KCY KRX KCX)).
  - exact (two_sphere_cylinder_change_base_unit X KRX KCX KRX KCX
      (fst (A 0).2 b)).
Defined.

(** Product preservation reuses the original corrected class inverse law.
    Only X needs missing-face-two comparison; products remain independent. *)

(** 乘积保持复用原校正类逆定律；只有 X 需要缺第二面比较，乘积选择仍独立。 *)

Lemma two_sphere_cylinder_inverse_mul
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS Y (α 0 b))
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_inverse_resp (two_sphere_kan_mul Y (α 0 b) H x y))
      (two_sphere_kan_mul X b K (two_sphere_cylinder_inverse_resp x)
        (two_sphere_cylinder_inverse_resp y)).
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KRX KCX)
    _ _ (two_sphere_class_inverse_mul α A b H K x y)).
Defined.

(** Map a supplied Y left candidate into the intermediate X group, then
    apply the existing base-change inverse law. Only the Y left choice
    is used; no Y product, right choice or Group is required. *)

(** 将给定 Y 左候选映入中间 X 群，再应用既有换基逆定律；Y 只使用左选择，
    不要求 Y 乘法、右选择或群。 *)

Lemma two_sphere_cylinder_inverse_left_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS Y (α 0 b))
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_inverse_resp
        (@SphereKanLeftInverse Y (α 0 b) I x).1)
      (@inv _ (hasGroup (TwoSphereCylinderGroup X b KRX KCX H K L))
        (two_sphere_cylinder_inverse_resp x)).
Proof.
  assert (E : (two_sphere_class_inverse_resp α A b
      (@SphereKanLeftInverse Y (α 0 b) I x).1 : TwoSphereClassS X b) ≈S
      @inv _ (hasGroup (TwoSphereClassGroup X b H K L))
        (two_sphere_class_inverse_resp α A b x)).
  { unfold two_sphere_class_inverse_resp.
    transitivity (two_sphere_class_change_base_resp X (fst (A 0).2 b)
      (@inv _ (hasGroup (TwoSphereClassGroup X ((α ^-1N A) 0 (α 0 b)) H K L))
        (two_sphere_class_map_resp (α ^-1N A) (α 0 b) x))).
    - exact (@func_proper _ _
        (two_sphere_class_change_base_resp X (fst (A 0).2 b)) _ _
        (two_sphere_class_map_left_inverse (α ^-1N A) (α 0 b) I H K L x)).
    - exact (two_sphere_class_change_base_left_inverse X
        (fst (A 0).2 b) K H K L
        (two_sphere_class_map_resp (α ^-1N A) (α 0 b) x)). }
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KRX KCX)
    _ _ E).
Defined.

(** Compose the existing class isomorphism with the two comparisons at
    independent common upward bounds. Its maps retain the forward image
    and the corrected inverse representatives just described. *)

(** 在独立共同向上界处，将既有类同构与两份比较复合；其映射保留前述正向像及
    校正逆代表。 *)

Definition two_sphere_cylinder_iso@{v q +}
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS Y (α 0 b) KRY KCY)
  := iso_trans (iso_symm (two_sphere_cylinder_class_iso X b KRX KCX))
      (iso_trans (two_sphere_class_iso α A b)
        (two_sphere_cylinder_class_iso Y (α 0 b) KRY KCY)).

End CylinderIsomorphism.
