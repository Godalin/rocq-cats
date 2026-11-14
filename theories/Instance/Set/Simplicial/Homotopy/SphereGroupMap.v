From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereMap
  Instance.Set.Simplicial.Homotopy.SphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Sphere-Class Operations under Maps and Equal-Base Transport

    The class maps of [SphereMap] already retain image triangles and
    actual composition tetrahedra. A map need not preserve a chosen horn
    filler: compare its image composite with the independently selected
    target composite using
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKanComparison.two_sphere_composite_output_eq}
    {%[two_sphere_composite_output_eq]%}%. Only the target needs the
    four-dimensional missing-face-two comparison choice.

    Equal-base transport works in the same way. Together these results
    apply to the existing corrected inverse of a natural isomorphism.
    For inverses, map the actual left-candidate tetrahedron and reuse
    [group_inv_unique] in the target group; a source group is unnecessary.
    All laws use generated class equality, without comparing selections,
    tetrahedra or boundary witnesses. Arbitrary-path basepoint transport,
    general Kan commutativity and π₂ identification remain further work. *)

(** * 映射及相等基点运输下的球面类运算

    [SphereMap] 的类映射已经保留像三角形及实际合成四面体。映射无需保持
    选定 horn 填充：用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKanComparison.two_sphere_composite_output_eq}
    {%[two_sphere_composite_output_eq]%}% 比较其像合成与独立选择的目标合成。
    只有目标需要四维缺第二面的比较选择。

    相等基点运输同样处理。这些结果共同适用于自然同构已有的带基点校正的
    逆映射。对于逆，映射实际左候选四面体，再在目标群中复用
    [group_inv_unique]，无需来源群。所有定律使用生成类相等，不比较选择、
    四面体或边界见证。任意路径换基、一般 Kan 交换性及 π₂ 识别仍需后续工作。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereClass}_2(X,b)^2
  \arrow[r,"\mu_X"] \arrow[d,"{\alpha_*\times\alpha_*}"'] &
\operatorname{SphereClass}_2(X,b) \arrow[d,"\alpha_*"] \\
\operatorname{SphereClass}_2(Y,\alpha_0b)^2
  \arrow[r,"\mu_Y"'] & \operatorname{SphereClass}_2(Y,\alpha_0b)
\end{tikzcd}
\end{center}%
*)

(** ** Mapping Selected Products

    Fix independent common ambient bounds and an arbitrary simplicial
    map. Three-dimensional multiplication choices are independent; the
    source needs no four-dimensional choice or selected algebra structure. *)

(** ** 映射选定乘积

    固定独立共同环境界及任意单纯映射。三维乘法选择相互独立；来源无需四维
    选择或选定代数结构。 *)

Section SphereMapProducts.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}.

(** Compare the image of the source composite with the target choice. *)

(** 比较来源合成的像与目标选择。 *)

Lemma two_sphere_class_map_mul (α : X ⇒ Y) (b : X 0)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺)
    (x y : TwoSphereClassS X b)
  : two_sphere_class_map_resp α b (two_sphere_kan_mul X b H x y) ≈S
      two_sphere_kan_mul Y (α 0 b) K
        (two_sphere_class_map_resp α b x)
        (two_sphere_class_map_resp α b y).
Proof.
  exact (two_sphere_composite_output_eq Y (α 0 b)
    (two_sphere_composite_map α b (TwoSphereKanMulComposite X b H x y))
    (TwoSphereKanMulComposite Y (α 0 b) K _ _)).
Defined.

End SphereMapProducts.

(** ** Products and the Unit at Equal Base Vertices

    Fix one simplicial setoid and a specified equality of vertices. Unit
    transport needs no fillers; product transport needs only the existing
    missing-face-two output comparison and two independent product choices. *)

(** ** 相等基点顶点处的乘积与单位

    固定一个单纯广集及顶点的指定相等。单位运输无需填充；乘积运输只需既有
    缺第二面输出比较及两份独立乘法选择。 *)

Section SphereEqualBaseProducts.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

(** Equality transport takes the actual constant sphere to the new unit. *)

(** 相等运输将实际常值球面送到新的单位。 *)

Lemma two_sphere_class_change_base_unit {b c : X 0} (E : b ≈S c)
  : two_sphere_class_change_base_resp X E (two_sphere_base X b) ≈S
      two_sphere_base X c.
Proof.
  apply two_sphere_class_eq. exact (simplex_constant_vertex_eq X E 2).
Defined.

(** Transport the retained tetrahedron before comparing output classes. *)

(** 先运输保留四面体，再比较输出类。 *)

Lemma two_sphere_class_change_base_mul
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    {b c : X 0} (E : b ≈S c)
    (H K : HasHornFillers X 3 fin_first⁺⁺)
    (x y : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp X E
      (two_sphere_kan_mul X b H x y) ≈S
      two_sphere_kan_mul X c K (two_sphere_class_change_base_resp X E x)
        (two_sphere_class_change_base_resp X E y).
Proof.
  exact (two_sphere_composite_output_eq X c
    (two_sphere_composite_change_base X E
      (TwoSphereKanMulComposite X b H x y))
    (TwoSphereKanMulComposite X c K _ _)).
Defined.

End SphereEqualBaseProducts.

(** ** Actual Left Candidates and the Target Group Inverse

    Fix a target with just the choices defining its existing class group.
    A supplied composite into the actual constant sphere is a left inverse
    by output comparison. Generic uniqueness does the remaining algebra;
    no source multiplication, source group or respectful filler selection
    is needed to map a left candidate. *)

(** ** 实际左候选与目标群逆

    固定目标及定义其既有类群的选择。给定合成若输出实际常值球面，则由输出
    比较给出左逆；剩余代数步骤使用通用唯一性。映射左候选不需要来源乘法、
    来源群或保相等填充选择。 *)

Section SphereTargetInverse.
Universes u p.
Context (Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (c : Y 0).
Context `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}.
Context `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}.
Context `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}.
Context (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺).

(** Read any actual left-inverse tetrahedron using the existing group. *)

(** 用既有群读取任意实际左逆四面体。 *)

Lemma two_sphere_composite_group_inverse {x y : TwoSphereS Y c}
    (W : TwoSphereComposite Y c y x (two_sphere_base Y c))
  : (y : TwoSphereClassS Y c) ≈S
      @group_inv _ (TwoSphereClassGroup Y c H K L) x.
Proof.
  apply (@group_inv_unique _ (TwoSphereClassGroup Y c H K L) x y).
  exact (two_sphere_composite_output_eq Y c
    (TwoSphereKanMulComposite Y c H y x) W).
Defined.

End SphereTargetInverse.

(** ** Mapping Inverse Candidates

    Fix independent common ambient sizes. The target has explicit class
    group choices; the source supplies only a three-dimensional left
    candidate. Correct the mapped constant output in its native equality
    before applying the preceding uniqueness consequence. *)

(** ** 映射逆候选

    固定独立共同环境大小。目标显式给出类群选择，来源仅给出三维左候选。
    先按原有相等校正像常值输出，再应用前面的唯一性推论。 *)

Section SphereMapInverses.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}.
Context `{HY3 : !HasHornFillers Y 4 fin_first⁺⁺⁺}.
Context `{HY4 : !HasHornFillers Y 4 fin_first⁺⁺⁺⁺}.

(** The image of an actual source left candidate is the target inverse. *)

(** 实际来源左候选的像为目标逆。 *)

Lemma two_sphere_class_map_left_inverse (α : X ⇒ Y) (b : X 0)
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers Y 3 fin_first⁺⁺⁺)
    (L : HasHornFillers Y 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : two_sphere_class_map_resp α b (@SphereKanLeftInverse X b I x).1 ≈S
      @group_inv _ (TwoSphereClassGroup Y (α 0 b) H K L)
        (two_sphere_class_map_resp α b x).
Proof.
  apply (two_sphere_composite_group_inverse Y (α 0 b) H K L).
  refine (TwoSphereCompositeChangeEndpoints Y (α 0 b)
    (two_sphere_composite_map α b (@SphereKanLeftInverse X b I x).2)
    (reflexivity _) (reflexivity _) _).
  apply simplex_constant_natural.
Defined.

End SphereMapInverses.

(** ** Inverse Candidates under Equal-Base Transport

    Fix one simplicial setoid with target group choices. Only the source
    left-candidate selection is used, independently of target selections.
    The vertex equality is specified setoid equality, not a path. *)

(** ** 相等基点运输下的逆候选

    固定一个单纯广集及目标群选择。来源只使用左候选选择，与目标选择独立。
    顶点相等是指定广集相等，并非路径。 *)

Section SphereEqualBaseInverses.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.

(** Transport retains the inverse tetrahedron and corrects its constant. *)

(** 运输保留逆四面体，并校正其常值输出。 *)

Lemma two_sphere_class_change_base_left_inverse {b c : X 0} (E : b ≈S c)
    (I : HasHornFillers X 3 fin_first⁺⁺⁺)
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
    (x : TwoSphereClassS X b)
  : two_sphere_class_change_base_resp X E
      (@SphereKanLeftInverse X b I x).1 ≈S
      @group_inv _ (TwoSphereClassGroup X c H K L)
        (two_sphere_class_change_base_resp X E x).
Proof.
  apply (two_sphere_composite_group_inverse X c H K L).
  refine (TwoSphereCompositeChangeEndpoints X c
    (two_sphere_composite_change_base X E
      (@SphereKanLeftInverse X b I x).2)
    (reflexivity _) (reflexivity _) _).
  exact (simplex_constant_vertex_eq X E 2).
Defined.

End SphereEqualBaseInverses.

(** ** The Existing Corrected Inverse Preserves Products

    Fix a natural isomorphism and independent multiplication choices.
    The already constructed inverse first maps by the inverse natural
    transformation, then corrects its base by vertex equality. Apply the
    two product laws to those same maps; no new inverse is constructed. *)

(** ** 既有校正逆保持乘积

    固定自然同构及独立乘法选择。已有逆先沿逆自然变换映射，再用顶点相等
    校正基点。将两个乘积定律应用于同样的映射，不重新构造逆。 *)

Section SphereIsomorphismProducts.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.

(** The same base-corrected inverse of [two_sphere_class_iso] is used. *)

(** 使用 [two_sphere_class_iso] 的同一个带基点校正的逆。 *)

Lemma two_sphere_class_inverse_mul (α : X ⇒ Y) (A : α ⦂ X ≅N Y)
    (b : X 0) (H : HasHornFillers Y 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺)
    (x y : TwoSphereClassS Y (α 0 b))
  : two_sphere_class_inverse_resp α A b
      (two_sphere_kan_mul Y (α 0 b) H x y) ≈S
      two_sphere_kan_mul X b K (two_sphere_class_inverse_resp α A b x)
        (two_sphere_class_inverse_resp α A b y).
Proof.
  unfold two_sphere_class_inverse_resp.
  transitivity (two_sphere_class_change_base_resp X (fst (A 0).2 b)
    (two_sphere_kan_mul X ((α ^-1N A) 0 (α 0 b)) K
      (two_sphere_class_map_resp (α ^-1N A) (α 0 b) x)
      (two_sphere_class_map_resp (α ^-1N A) (α 0 b) y))).
  - exact (@func_proper _ _
      (two_sphere_class_change_base_resp X (fst (A 0).2 b)) _ _
      (two_sphere_class_map_mul (α ^-1N A) (α 0 b) H K x y)).
  - exact (two_sphere_class_change_base_mul X (fst (A 0).2 b) K K _ _).
Defined.

End SphereIsomorphismProducts.
