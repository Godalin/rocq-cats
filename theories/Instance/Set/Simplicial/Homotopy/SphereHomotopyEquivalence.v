From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereBasedHomotopyClass.
From Cats Require Import
  Cat.Core
  Cat.Natural
  Instance.Set.Isomorphism.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Based Homotopy Inverses Preserve Sphere Classes

    A reverse simplicial map need not be a strict inverse. An actual
    composite-to-identity homotopy with constant base trajectory suffices
    on sphere classes: apply
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereBasedHomotopyClass.two_sphere_class_map_homotopy}
    {%[two_sphere_class_map_homotopy]%}% to that composite. The trajectory
    itself determines the correction from the reverse image base back to
    the original base. No extra pointed-map structure is introduced. *)

(** * 实际基点同伦逆保持球面类

    反向单纯映射未必严格互逆。若实际复合到恒等的同伦具有常值基点轨迹，
    则对该复合应用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereBasedHomotopyClass.two_sphere_class_map_homotopy}
    {%[two_sphere_class_map_homotopy]%}% 即可在球面类上恢复互逆。
    轨迹本身确定从反向像基点返回原基点的校正，无需新建基点映射结构。 *)

(** ** A Corrected Reverse Map and Two Independent Round Trips

    Fix arbitrary forward/reverse maps and a source vertex. One actual
    homotopy and its constant trajectory define the reverse class map
    without filling choices. Its left inverse law only uses comparison
    choices in X; a second homotopy gives the right law using choices in Y.
    Thus no Group, three-dimensional choices or full Kan structure enter.
    The diagram commutes in generated class equality, not native equality
    of triangles. Arbitrary paths and weak equivalences are not covered. *)

(** ** 校正反向映射与两个独立往返

    固定任意正反向映射及源顶点。一实际同伦及其常值轨迹无需填充选择就确定
    反向类映射。左逆律仅用 X 的比较选择；第二个同伦仅用 Y 的选择给出右律。
    不需要群、三维选择或完整 Kan。下图按生成类相等交换，不要求三角形原生
    相等。本结果不涉及任意路径或弱等价。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereClass}_2(X,b)
  \arrow[r,"{f_*}"] \arrow[dr,"{\mathrm{id}}"'] &
\operatorname{SphereClass}_2(Y,f_0b)
  \arrow[d,"{(e_H)_*\,g_*}"] \\
& \operatorname{SphereClass}_2(X,b)
\end{tikzcd}
\end{center}%
*)

Section SphereHomotopyEquivalence.
Universes u p.
Context {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (f : X ⇒ Y) (g : Y ⇒ X) (b : X 0).
Context (H : SimplicialHomotopy (g ∘Nv f) (idN : X ⇒ X)).
Context (E : homotopy_map H 1 (simplex_constant X b 1, simplex_generic 1)
  ≈S simplex_constant X b 1).

(** Apply g, then transport along the base equality derived from H.
    Both operations are the existing respectful class maps. *)

(** 先应用 g，再沿 H 导出的基点相等运输；两步均为既有保相等类映射。 *)

Definition two_sphere_class_homotopy_inverse_resp
  : TwoSphereClassS Y (f 0 b) →r TwoSphereClassS X b
  := two_sphere_class_change_base_resp X
      (sphere_homotopy_base H b b E false) ∘r
      two_sphere_class_map_resp g (f 0 b).

(** Only X needs dimension-four missing-face-one/two comparisons.
    First use composition coherence, then the actual based homotopy. *)

(** 仅 X 需要四维缺第一／第二面的比较；先用复合相干性，再用实际基点同伦。 *)

Lemma two_sphere_class_homotopy_inverse_l
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (x : TwoSphereClassS X b)
  : two_sphere_class_homotopy_inverse_resp
      (two_sphere_class_map_resp f b x) ≈S x.
Proof.
  transitivity (two_sphere_class_change_base_resp X
    (sphere_homotopy_base H b b E false)
    (two_sphere_class_map_resp (g ∘Nv f) b x)).
  - apply (@func_proper _ _ (two_sphere_class_change_base_resp X
      (sphere_homotopy_base H b b E false))).
    symmetry. apply two_sphere_class_map_comp.
  - transitivity (two_sphere_class_change_base_resp X
      (sphere_homotopy_base H b b E true)
      (two_sphere_class_map_resp (idN : X ⇒ X) b x)).
    + exact (two_sphere_class_map_homotopy H b b E x).
    + transitivity (two_sphere_class_change_base_resp X (reflexivity b)
        (two_sphere_class_map_resp (idN : X ⇒ X) b x)).
      * apply two_sphere_class_change_base_witness.
      * transitivity (two_sphere_class_map_resp (idN : X ⇒ X) b x).
        -- apply two_sphere_class_change_base_id.
        -- apply two_sphere_class_map_id.
Defined.

(** The left inverse reflects generated equality, using respectfulness
    of the same reverse map. No choices in Y are needed. *)

(** 同一反向映射的保相等性与左逆律反映生成相等，无需 Y 中的选择。 *)

Lemma two_sphere_class_map_homotopy_reflect
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    (x y : TwoSphereClassS X b)
    (F : two_sphere_class_map_resp f b x ≈S two_sphere_class_map_resp f b y)
  : x ≈S y.
Proof.
  transitivity (two_sphere_class_homotopy_inverse_resp
    (two_sphere_class_map_resp f b x)).
  - symmetry. apply two_sphere_class_homotopy_inverse_l.
  - transitivity (two_sphere_class_homotopy_inverse_resp
      (two_sphere_class_map_resp f b y)).
    + apply (@func_proper _ _ two_sphere_class_homotopy_inverse_resp).
      exact F.
    + apply two_sphere_class_homotopy_inverse_l.
Defined.

(** The other composite-to-identity homotopy only needs target comparison
    choices. Base-transport naturality and witness independence align its
    derived correction with the image of the first correction; no equation
    between the two homotopies or their proof fields is assumed. *)

(** 另一复合到恒等的同伦仅需目标比较选择。换基点自然性及见证无关性将其
    派生校正与首个校正的像对齐，不要求两个同伦或其证明字段之间的方程。 *)

Lemma two_sphere_class_homotopy_inverse_r
    (K : SimplicialHomotopy (f ∘Nv g) (idN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
    (y : TwoSphereClassS Y (f 0 b))
  : two_sphere_class_map_resp f b
      (two_sphere_class_homotopy_inverse_resp y) ≈S y.
Proof.
  transitivity (two_sphere_class_change_base_resp Y
    (@func_proper _ _ (f 0) _ _ (sphere_homotopy_base H b b E false))
    (two_sphere_class_map_resp f (g 0 (f 0 b))
      (two_sphere_class_map_resp g (f 0 b) y))).
  - symmetry. apply two_sphere_class_map_change_base.
  - transitivity (two_sphere_class_change_base_resp Y
      (@func_proper _ _ (f 0) _ _ (sphere_homotopy_base H b b E false))
      (two_sphere_class_map_resp (f ∘Nv g) (f 0 b) y)).
    + apply (@func_proper _ _ (two_sphere_class_change_base_resp Y
        (@func_proper _ _ (f 0) _ _
          (sphere_homotopy_base H b b E false)))).
      symmetry. exact (two_sphere_class_map_comp g f (f 0 b) y).
    + transitivity (two_sphere_class_change_base_resp Y
        (sphere_homotopy_base K (f 0 b) (f 0 b) F false)
        (two_sphere_class_map_resp (f ∘Nv g) (f 0 b) y)).
      * apply two_sphere_class_change_base_witness.
      * transitivity (two_sphere_class_change_base_resp Y
          (sphere_homotopy_base K (f 0 b) (f 0 b) F true)
          (two_sphere_class_map_resp (idN : Y ⇒ Y) (f 0 b) y)).
        -- exact (two_sphere_class_map_homotopy K (f 0 b) (f 0 b) F y).
        -- transitivity (two_sphere_class_change_base_resp Y
            (reflexivity (f 0 b))
            (two_sphere_class_map_resp (idN : Y ⇒ Y) (f 0 b) y)).
           ++ apply two_sphere_class_change_base_witness.
           ++ transitivity
               (two_sphere_class_map_resp (idN : Y ⇒ Y) (f 0 b) y).
              ** apply two_sphere_class_change_base_id.
              ** apply two_sphere_class_map_id.
Defined.

(** Both actual homotopies give a setoid isomorphism at independent common
    upward carrier/equality bounds. The maps remain the existing f-map
    and corrected g-map; no resizing, Group or strict inverse is required. *)

(** 两个实际同伦在独立共同向上载体／相等界处给出广集同构。映射仍为既有
    f 映射与校正 g 映射，无需大小重设、群或严格逆。 *)

Definition two_sphere_class_homotopy_iso@{v q +}
    (K : SimplicialHomotopy (f ∘Nv g) (idN : Y ⇒ Y))
    (F : homotopy_map K 1
      (simplex_constant Y (f 0 b) 1, simplex_generic 1)
      ≈S simplex_constant Y (f 0 b) 1)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HY1 : !HasHornFillers Y 4 fin_first⁺}
    `{HY2 : !HasHornFillers Y 4 fin_first⁺⁺}
  : LiftS@{_ _ v q} (TwoSphereClassS X b)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereClassS Y (f 0 b)).
Proof.
  exists ((two_sphere_class_map_resp f b)^↑S),
    (two_sphere_class_homotopy_inverse_resp^↑S).
  split.
  - intros [x]. exact {|lower := two_sphere_class_homotopy_inverse_l x|}.
  - intros [y]. exact {|lower := two_sphere_class_homotopy_inverse_r K F y|}.
Defined.

End SphereHomotopyEquivalence.

(** The actual-cylinder presentation of these same corrected maps and round
    trips is developed in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderHomotopy.two_sphere_cylinder_homotopy_iso}
    {%[two_sphere_cylinder_homotopy_iso]%}%. That comparison reuses the
    missing-face-one/two choices already contained in its presentations;
    both constant-trajectory hypotheses remain explicit. *)

(** 同样校正映射及往返的实际柱呈现见
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderHomotopy.two_sphere_cylinder_homotopy_iso}
    {%[two_sphere_cylinder_homotopy_iso]%}%。该比较复用呈现中已有的缺第一／第二面
    选择，并显式保留两个常值轨迹前提。 *)
