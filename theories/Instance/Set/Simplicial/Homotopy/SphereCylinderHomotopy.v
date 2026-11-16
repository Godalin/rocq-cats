From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinderBase
  Instance.Set.Simplicial.Homotopy.SphereHomotopyEquivalence.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Based Homotopy Inverses in the Cylinder Presentation

    Replace the natural-isomorphism hypothesis by actual maps [f] and [g]
    and two composite-to-identity homotopies. Each base trajectory must be
    specified equal to the constant edge. The first trajectory derives
    the correction from [g 0 (f 0 b)] to [b]; it does not supply arbitrary
    path transport. Compose the existing cylinder g-map and equal-base
    transport to retain the original corrected class representative.

    Reuse
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereHomotopyEquivalence.two_sphere_class_homotopy_iso}
    {%[two_sphere_class_homotopy_iso]%}% for round trips, reflection and
    the common-lift comparison. Missing-face-one/two comparisons already
    occur at zero-based entries four/six of each reversal family KR, so
    these conclusions add no filling choices. No coherence equation
    between the homotopies or their trajectory witnesses is required.

    Existing map/base operation laws apply to this same corrected reverse;
    compose class equations before constructing the inverse-law cylinder.
    The forward map keeps its original operation laws. Presentations and
    algebra choices remain independent and explicit. No new pointed-map
    or group-hom interface, global model, witness round-trip equality or
    filler preservation is introduced. General Kan commutativity/π₂,
    arbitrary paths and arbitrary weak-equivalence chains remain open. *)

(** * 实际柱呈现中的基点同伦逆

    用实际映射 [f]、[g] 及两个复合到恒等同伦替代自然同构前提。每条基点轨迹
    须指定等于常值边。第一条轨迹导出从 [g 0 (f 0 b)] 到 [b] 的校正，不提供
    任意路径运输。复合既有柱 g 映射及相等基点运输，保留原校正类代表。

    往返、反映及共同提升比较复用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereHomotopyEquivalence.two_sphere_class_homotopy_iso}
    {%[two_sphere_class_homotopy_iso]%}%。缺第一／第二面比较已在各反转族 KR
    从零计数的第四／第六项中，因此这些结论不增加填充选择；不要求两个同伦
    或轨迹见证之间满足相干方程。

    既有映射／换基运算定律适用于同一校正逆；逆律先复合类方程再构造柱。
    正向映射保留原运算定律。呈现与代数选择仍独立显式给出，不引入新的基点
    映射或群同态接口、全局模型、见证往返相等或填充保持。一般 Kan 交换性／π₂、
    任意路径及任意弱等价链仍保持开放。 *)

(** The lower arrow is corrected using the first constant trajectory.
    Both round trips commute by actual relative cylinders. *)

(** 下方箭头用第一条常值轨迹校正；两个往返均按实际相对柱交换。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereCyl}_2(X,b)
  \arrow[r,shift left,"f_*"] &
\operatorname{SphereCyl}_2(Y,f_0b)
  \arrow[l,shift left,"{(e_T)_*g_*}"]
\end{tikzcd}
\end{center}%
*)

(** ** Independent Actual Homotopies and Explicit Presentations

    Fix independent ambient bounds, the maps, first actual homotopy and
    its constant trajectory. Only right recovery and the isomorphism add
    the second homotopy/trajectory. All comparisons keep witnesses distinct. *)

(** ** 独立实际同伦及显式呈现

    固定独立环境界、两映射、首个实际同伦及其常值轨迹。只有右恢复及同构增加
    第二个同伦／轨迹；所有比较保持见证独立。 *)

Section CylinderHomotopyComparison.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0).
Context (T : SimplicialHomotopy (g ∘Nv f) (idN : X ⇒ X)).
Context (E : homotopy_map T 1 (simplex_constant X b 1, simplex_generic 1)
  ≈S simplex_constant X b 1).
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

(** First map by g, then correct its basepoint
    using the same X presentation at both X vertices. *)

(** 先沿 g 映射，再使用两个 X 顶点处的同一 X 呈现校正基点。 *)

Definition two_sphere_cylinder_homotopy_inverse_resp
  : TwoSphereCylinderS Y (f 0 b) KRY KCY →r TwoSphereCylinderS X b KRX KCX
  := two_sphere_cylinder_change_base_resp X KRX KCX KRX KCX
      (sphere_homotopy_base T b b E false) ∘r
      two_sphere_cylinder_map_resp g (f 0 b) KRY KCY KRX KCX.

(** The corrected inverse recovers a source sphere by an actual cylinder. *)

(** 校正逆按实际柱恢复来源球面。 *)

Lemma two_sphere_cylinder_homotopy_inverse_l (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_homotopy_inverse_resp
        (two_sphere_cylinder_map_resp f b KRX KCX KRY KCY x)) x.
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KRX KCX)
    _ _ (@two_sphere_class_homotopy_inverse_l X Y f g b T E
      (KRX fin_first⁺⁺⁺⁺) (KRX fin_first⁺⁺⁺⁺⁺⁺) x)).
Defined.

(** The original forward map recovers every target sphere after correction. *)

(** 原正向映射在校正后恢复每个目标球面。 *)

Lemma two_sphere_cylinder_homotopy_inverse_r
    (U : SimplicialHomotopy (f ∘Nv g) (idN : Y ⇒ Y))
    (F : homotopy_map U 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    (y : TwoSphereS Y (f 0 b))
  : TwoSphereCylinderHomotopy Y (f 0 b)
      (two_sphere_cylinder_map_resp f b KRX KCX KRY KCY
        (two_sphere_cylinder_homotopy_inverse_resp y)) y.
Proof.
  exact (@func_proper _ _
    (two_sphere_cylinder_of_class_resp Y (f 0 b) KRY KCY)
    _ _ (@two_sphere_class_homotopy_inverse_r X Y f g b T E U F
      (KRY fin_first⁺⁺⁺⁺) (KRY fin_first⁺⁺⁺⁺⁺⁺) y)).
Defined.

(** Reflect an actual image cylinder through the original class reflection.
    Only the supplied left homotopy is used; no second homotopy is needed. *)

(** 经原类反映定理反映实际像柱；只使用给定左同伦，不需要第二个同伦。 *)

Lemma two_sphere_cylinder_homotopy_reflect (x y : TwoSphereS X b)
    (W : TwoSphereCylinderHomotopy Y (f 0 b)
      (two_sphere_cylinder_map_resp f b KRX KCX KRY KCY x)
      (two_sphere_cylinder_map_resp f b KRX KCX KRY KCY y))
  : TwoSphereCylinderHomotopy X b x y.
Proof.
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KRX KCX)
    _ _ (@two_sphere_class_map_homotopy_reflect X Y f g b T E
      (KRX fin_first⁺⁺⁺⁺) (KRX fin_first⁺⁺⁺⁺⁺⁺) x y
      (@func_proper _ _
        (two_sphere_class_of_cylinder_resp Y (f 0 b) KRY KCY) _ _ W))).
Defined.

(** Map the unit by g before applying base
    transport. Both existing unit laws need no algebra choice. *)

(** 先沿 g 映射单位，再作基点运输；两条既有单位律均不需代数选择。 *)

Lemma two_sphere_cylinder_homotopy_inverse_unit
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_homotopy_inverse_resp (two_sphere_base Y (f 0 b)))
      (two_sphere_base X b).
Proof.
  change ((two_sphere_cylinder_homotopy_inverse_resp
    (two_sphere_base Y (f 0 b)) : TwoSphereCylinderS X b KRX KCX) ≈S
    two_sphere_base X b).
  transitivity (two_sphere_cylinder_change_base_resp X KRX KCX KRX KCX
    (sphere_homotopy_base T b b E false) (two_sphere_base X (g 0 (f 0 b)))).
  - exact (@func_proper _ _
      (two_sphere_cylinder_change_base_resp X KRX KCX KRX KCX
        (sphere_homotopy_base T b b E false)) _ _
      (two_sphere_cylinder_map_unit g (f 0 b) KRY KCY KRX KCX)).
  - exact (two_sphere_cylinder_change_base_unit X KRX KCX KRX KCX
      (sphere_homotopy_base T b b E false)).
Defined.

(** Product preservation composes existing class map and base-change laws.
    Use the missing-face-two comparison already in KRX; the two product
    selections remain independent, with no additional comparison choice. *)

(** 乘积保持复合既有类映射及换基定律，使用 KRX 已有的缺第二面比较；两份乘积
    选择仍独立，不增加比较选择。 *)

Lemma two_sphere_cylinder_homotopy_inverse_mul
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺) (x y : TwoSphereS Y (f 0 b))
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_homotopy_inverse_resp (two_sphere_kan_mul Y (f 0 b) H x y))
      (two_sphere_kan_mul X b K (two_sphere_cylinder_homotopy_inverse_resp x)
        (two_sphere_cylinder_homotopy_inverse_resp y)).
Proof.
  assert (HX2 : HasHornFillers X 4 fin_first⁺⁺)
    by exact (KRX fin_first⁺⁺⁺⁺⁺⁺).
  assert (G : (two_sphere_class_homotopy_inverse_resp f g b T E
      (two_sphere_kan_mul Y (f 0 b) H x y) : TwoSphereClassS X b) ≈S
      two_sphere_kan_mul X b K
        (two_sphere_class_homotopy_inverse_resp f g b T E x)
        (two_sphere_class_homotopy_inverse_resp f g b T E y)).
  { unfold two_sphere_class_homotopy_inverse_resp.
    transitivity (two_sphere_class_change_base_resp X
      (sphere_homotopy_base T b b E false)
      (two_sphere_kan_mul X (g 0 (f 0 b)) K
        (two_sphere_class_map_resp g (f 0 b) x)
        (two_sphere_class_map_resp g (f 0 b) y))).
    - exact (@func_proper _ _ (two_sphere_class_change_base_resp X
        (sphere_homotopy_base T b b E false)) _ _
        (two_sphere_class_map_mul g (f 0 b) H K x y)).
    - exact (two_sphere_class_change_base_mul X
        (sphere_homotopy_base T b b E false) K K _ _). }
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KRX KCX)
    _ _ G).
Defined.

(** Map a supplied Y left candidate into the intermediate X group, then
    apply the existing base-change inverse law. Only the Y left choice
    is used; no Y product, right choice or Group is required. *)

(** 将给定 Y 左候选映入中间 X 群，再应用既有换基逆定律；Y 只使用左选择，
    不要求 Y 乘法、右选择或群。 *)

Lemma two_sphere_cylinder_homotopy_inverse_left_inverse
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}
    (I : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : TwoSphereS Y (f 0 b))
  : TwoSphereCylinderHomotopy X b
      (two_sphere_cylinder_homotopy_inverse_resp
        (@SphereKanLeftInverse Y (f 0 b) I x).1)
      (@inv _ (hasGroup (TwoSphereCylinderGroup X b KRX KCX H K L))
        (two_sphere_cylinder_homotopy_inverse_resp x)).
Proof.
  assert (G : (two_sphere_class_homotopy_inverse_resp f g b T E
      (@SphereKanLeftInverse Y (f 0 b) I x).1 : TwoSphereClassS X b) ≈S
      @inv _ (hasGroup (TwoSphereClassGroup X b H K L))
        (two_sphere_class_homotopy_inverse_resp f g b T E x)).
  { unfold two_sphere_class_homotopy_inverse_resp.
    transitivity (two_sphere_class_change_base_resp X (sphere_homotopy_base T b b E false)
      (@inv _ (hasGroup (TwoSphereClassGroup X (g 0 (f 0 b)) H K L))
        (two_sphere_class_map_resp g (f 0 b) x))).
    - exact (@func_proper _ _
        (two_sphere_class_change_base_resp X
          (sphere_homotopy_base T b b E false)) _ _
        (two_sphere_class_map_left_inverse g (f 0 b) I H K L x)).
    - exact (two_sphere_class_change_base_left_inverse X
        (sphere_homotopy_base T b b E false) K H K L
        (two_sphere_class_map_resp g (f 0 b) x)). }
  exact (@func_proper _ _ (two_sphere_cylinder_of_class_resp X b KRX KCX)
    _ _ G).
Defined.

(** Compose the existing class isomorphism with the two comparisons at
    independent common upward bounds. Its maps retain the forward image
    and the corrected inverse representatives just described. *)

(** 在独立共同向上界处，将既有类同构与两份比较复合；其映射保留前述正向像及
    校正逆代表。 *)

Definition two_sphere_cylinder_homotopy_iso@{v q +}
    (U : SimplicialHomotopy (f ∘Nv g) (idN : Y ⇒ Y))
    (F : homotopy_map U 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KRX KCX)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS Y (f 0 b) KRY KCY)
  := iso_trans (iso_symm (two_sphere_cylinder_class_iso X b KRX KCX))
      (iso_trans (@two_sphere_class_homotopy_iso X Y f g b T E U F
        (KRX fin_first⁺⁺⁺⁺) (KRX fin_first⁺⁺⁺⁺⁺⁺)
        (KRY fin_first⁺⁺⁺⁺) (KRY fin_first⁺⁺⁺⁺⁺⁺))
        (two_sphere_cylinder_class_iso Y (f 0 b) KRY KCY)).

End CylinderHomotopyComparison.
