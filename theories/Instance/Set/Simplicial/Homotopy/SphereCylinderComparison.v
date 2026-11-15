From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinderKan
  Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder
  Instance.Set.Simplicial.Homotopy.SphereCylinderClass.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Generated Chains and Actual Relative Cylinders

    Equality in [TwoSphereClassS] retains a finite derivation: specified
    sphere equalities, elementary tetrahedra, reversals and concatenations.
    It does not itself contain a map from the whole cylinder. Here the
    existing actual reversal/composition operations interpret that derivation
    as such a map, including its boundary law in every degree and time shape.

    There is one direction to check before folding: the three pieces of
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder.TwoSphereHomotopyCylinder}
    {%[TwoSphereHomotopyCylinder]%}% run from y to x for an elementary
    generator from x to y. Actual reversal corrects this direction.
    Then [equiv_closure_preserves] handles the entire derivation; no new
    recursion or quotient is introduced.

    The two explicit nine-choice families supply an explicit equivalence
    witness, never an automatically registered instance. The converse reuses
    the missing-face-one/two choices already present in the reversal family.
    The result is a pair of Type-valued witness transformations, not inverse
    equations for
    cylinder or derivation records. Choice independence, general Kan π₂,
    arbitrary paths and weak-equivalence comparisons remain separate. *)

(** * 生成链与实际相对柱

    [TwoSphereClassS] 的相等保留有限推导：指定球面相等、初等四面体、反向与
    串接；它本身并不包含整个柱上的映射。此处用已有实际反转／复合操作，将
    推导解释为这样的映射，同时保留任意维、任意时间形状处的完整边界律。

    折叠前须校正一次方向：对从x到y的初等生成元，
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder.TwoSphereHomotopyCylinder}
    {%[TwoSphereHomotopyCylinder]%}% 的三块实际从y走到x；实际反转将其改正。
    随后直接由 [equiv_closure_preserves] 处理整个推导，不另写递归或取商。

    两组显式九份选择给出显式等价见证，不自动注册实例。反方向复用反转选择族
    中已有的四维缺第一／第二面选择。结果是一对Type值见证转换，不要求柱记录
    或推导记录满足往返相等。选择独立、一般Kan π₂、任意路径及弱等价比较保持
    为独立目标。 *)

(** In the first diagram Π(w) is the three-piece cylinder and R is actual
    reversal; its two occurrences of x are the same supplied sphere.
    The second diagram names the fold Φ and prism descent Ψ. The arrows
    transform witnesses; they assert no inverse equations for these maps. *)

(** 首图Π(w)为三块柱，R为实际反转；两处x是同一个给定球面。次图Φ表示折叠，
    Ψ表示棱柱下降。箭头转换见证，不断言这些映射满足逆方程。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
x \arrow[r,"w"]
  & y \arrow[dl,"\Pi(w)"'] \\
x \arrow[ur,bend right=30,"{R\Pi(w)}"'] &
\end{tikzcd}
\qquad
\begin{tikzcd}[column sep=large,row sep=large]
{x\approx_{\mathrm{gen}}y}
  \arrow[r,shift left,"\Phi"]
& {H:x\rightsquigarrow y\;\mathrm{rel}\;\partial\Delta[2]}
  \arrow[l,shift left,"\Psi"]
\end{tikzcd}
\end{center}%
*)

(** ** Interpreting Finite Generated Derivations

    Fix independent carrier/equality bounds, a base vertex and precisely
    the two nine-choice families for reversing and composing cylinders.
    Keep the resulting equivalence value explicit. *)

(** ** 解释有限生成推导

    固定独立载体／相等界、基点及反转／复合柱各自对应的九份选择。
    所得等价结构始终作为显式值使用。 *)

Section GeneratedCylinders.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** Reflexivity is constant; symmetry and transitivity are the actual
    selected relative cylinders. No global instance is declared. *)

(** 自反由常值柱给出，对称与传递由实际选定相对柱给出；不声明全局实例。 *)

Definition TwoSphereCylinderEquivalence
  : Equivalence (TwoSphereCylinderHomotopy X b).
Proof.
  split.
  - intro x. exact (TwoSphereConstantCylinder X b x x (reflexivity x)).
  - intros x y H. exact (SphereCylinderReverse X b KR H).
  - intros x y z H L. exact (SphereCylinderComposite X b KC H L).
Defined.

(** Correct the elementary prism's reversed direction using only KR. *)

(** 只用KR，将初等棱柱的反向方向校正。 *)

Definition TwoSphereElementaryForwardCylinder {x y : TwoSphereS X b}
    (H : TwoSphereHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b x y
  := SphereCylinderReverse X b KR (TwoSphereHomotopyCylinder X b H).

(** Reuse the general closure fold with the explicit equivalence value.
    Both kinds of generator retain actual maps and full relative laws. *)

(** 以显式等价值复用通用闭包折叠；两类生成元都保留实际映射及完整相对律。 *)

Definition TwoSphereClassCylinder {x y : TwoSphereS X b}
    (H : (x : TwoSphereClassS X b) ≈S y)
  : TwoSphereCylinderHomotopy X b x y.
Proof.
  refine (@equiv_closure_preserves _ _ _ _
    TwoSphereCylinderEquivalence (λ x, x) _ x y H).
  intros a c [E | E].
  - exact (TwoSphereConstantCylinder X b a c E).
  - exact (TwoSphereElementaryForwardCylinder E).
Defined.

End GeneratedCylinders.

(** ** Comparing the Two Existence Relations

    The existing cylinder-to-class theorem needs four-dimensional missing
    faces one/two. These are already entries four/six of KR (counted from
    zero), so no further choices are added. No selected multiplication,
    Group structure, automatic Kan or equality of witnesses is needed. *)

(** ** 比较两种存在关系

    已有柱到类定理需要四维缺第一／第二面；它们已经是KR中从零计数的第四／第六项，
    无需添加选择，也无需选定乘法、群结构、自动Kan或见证相等。 *)

Section CylinderClassComparison.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
(** Actual full relative cylinders and finite generated class equality
    imply each other. The maps need not recover the original witnesses. *)

(** 实际完整相对柱与有限生成类相等互相推出；转换不必恢复原见证。 *)

Definition two_sphere_cylinder_class_iff (x y : TwoSphereS X b)
  : TwoSphereCylinderHomotopy X b x y ↔
      (x : TwoSphereClassS X b) ≈S y
  := (@two_sphere_cylinder_class X b
        (KR fin_first⁺⁺⁺⁺) (KR fin_first⁺⁺⁺⁺⁺⁺) x y,
      TwoSphereClassCylinder X b KR KC).

End CylinderClassComparison.
