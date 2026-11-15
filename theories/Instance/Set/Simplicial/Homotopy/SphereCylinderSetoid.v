From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinderComparison.
From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMap
  Instance.Set.Isomorphism
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Setoid Presentation by Actual Relative Cylinders

    The preceding comparison identifies two existence relations on the same
    based triangles: a finite generated derivation, or an actual full
    relative cylinder. We now expose the latter as an explicitly enabled
    setoid. A representative is still a triangle with its boundary witnesses;
    equality stores the whole cylinder map and its relative boundary law.
    No quotient type or second generated closure is introduced.

    The existing [TwoSphereClassS] remains the primary class presentation.
    The two identity-on-representatives maps below reuse
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderComparison.two_sphere_cylinder_class_iff}
    {%[two_sphere_cylinder_class_iff]%}% for respectfulness. Their element
    round trips give a setoid isomorphism after independent common upward
    lifts. This does not require inverse equations for the equality witnesses.

    Independent enabling choices are compared by composing these same
    isomorphisms. Only their representative maps are compared; selected
    fillers and constructed cylinder witnesses need not be equal. This
    presentation alone proves no commutativity, general π₂ identification,
    arbitrary-path transport or weak-equivalence invariant. *)

(** * 以实际相对柱呈现广集

    前一比较在同一批基点三角形上接通两种存在关系：有限生成推导，或实际完整
    相对柱。现在将后者显式组成广集。代表仍为带边界见证的三角形；相等则保存
    整个柱映射与相对边界律，不构造商类型或第二份生成闭包。

    既有 [TwoSphereClassS] 仍是类的主呈现。下方两份保持代表的恒等映射，复用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinderComparison.two_sphere_cylinder_class_iff}
    {%[two_sphere_cylinder_class_iff]%}% 证明保相等；其元素往返律在独立共同向上
    提升后给出广集同构，不要求相等见证满足逆方程。

    独立启用选择的比较，直接复合这些相同同构。只比较代表映射，不等同所选
    填充或构造的柱见证。这个呈现本身不证明交换性、一般π₂识别、任意路径运输
    或弱等价不变量。 *)

(** The horizontal arrows retain the representative. Φ interprets generated
    equality as a cylinder, while Ψ reads a cylinder as generated equality.
    The inverse equations concern elements, not Φ/Ψ on equality witnesses. *)

(** 水平箭头保留代表；Φ将生成相等解释为柱，Ψ将柱读成生成相等。互逆方程
    针对元素，不针对Φ／Ψ对相等见证的作用。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
{(\operatorname{Sphere}_2,\approx_{\mathrm{gen}})}
  \arrow[r,shift left,"{1,\Phi}"]
& {(\operatorname{Sphere}_2,\approx_{\mathrm{cyl}})}
  \arrow[l,shift left,"{1,\Psi}"]
\end{tikzcd}
\end{center}%
*)

(** ** Explicit Presentation and the Same Representatives

    Fix independent simplex carrier/equality sizes, a base vertex and the
    two nine-choice families. They supply equivalence laws explicitly;
    importing this module selects no setoid model or cylinder instance. *)

(** ** 显式呈现与相同代表

    固定独立单形载体／相等大小、基点及两组九份选择。它们显式提供等价律；
    导入模块不选择广集模型或柱关系实例。 *)

Section CylinderPresentation.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).

(** Equality is the original actual relative-cylinder type. Only its
    equivalence laws use the supplied choices. No new relation is defined. *)

(** 相等就是原来的实际相对柱类型，只有其等价律使用给定选择；不另定义关系。 *)

Program Definition TwoSphereCylinderS
  : SetC
  :=
  {|carrier := TwoSphereS X b
  ; carrier_equiv := TwoSphereCylinderHomotopy X b
  ; carrier_setoid := TwoSphereCylinderEquivalence X b KR KC
  |}.

(** Keep the triangle and fold a generated equality into an actual cylinder. *)

(** 保持三角形，将生成相等折叠为实际柱。 *)

Program Definition two_sphere_cylinder_of_class_resp
  : TwoSphereClassS X b →r TwoSphereCylinderS
  :=
  {|func x := x
  |}.
Next Obligation.
  intros x y H. exact (TwoSphereClassCylinder X b KR KC H).
Defined.

(** Keep the triangle and use the accepted prism descent on its equality. *)

(** 保持三角形，在其相等见证上使用已验收的棱柱下降。 *)

Program Definition two_sphere_class_of_cylinder_resp
  : TwoSphereCylinderS →r TwoSphereClassS X b
  :=
  {|func x := x
  |}.
Next Obligation.
  intros x y H. exact (fst (two_sphere_cylinder_class_iff X b KR KC x y) H).
Defined.

(** Common upward bounds contain both native equality types. The two maps
    retain exactly the same representatives; no resizing principle is used. *)

(** 共同向上界容纳两种原生大小的相等类型；两个映射保留相同代表，不用大小重设。 *)

Definition two_sphere_cylinder_class_iso@{v q +}
  : LiftS@{_ _ v q} (TwoSphereClassS X b)
      ≅[SetCat@{v q _ _ _ _ _}] LiftS@{_ _ v q} TwoSphereCylinderS.
Proof.
  exists (two_sphere_cylinder_of_class_resp^↑S),
    (two_sphere_class_of_cylinder_resp^↑S).
  split; intros [x]; refine {|lower := _|}; reflexivity.
Defined.

End CylinderPresentation.

(** Compare two explicit enabling choices through the primary class
    presentation, reusing generic inverse/composition of isomorphisms.
    This compares representative maps, not chosen filling functions. *)

(** 经主类呈现比较两组显式启用选择，复用一般同构取逆／复合；比较的是代表映射，
    不是选定填充函数。 *)

Definition two_sphere_cylinder_choice_iso@{u p v q +}
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (KR : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
    (KC : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first⁺ s))
    (KR' : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
    (KC' : ∀ s, HasHornFillers X
      (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first⁺ s))
  : LiftS@{_ _ v q} (TwoSphereCylinderS X b KR KC)
      ≅[SetCat@{v q _ _ _ _ _}]
      LiftS@{_ _ v q} (TwoSphereCylinderS X b KR' KC')
  := iso_trans (iso_symm (two_sphere_cylinder_class_iso X b KR KC))
      (two_sphere_cylinder_class_iso X b KR' KC').

(** ** Mapping the Explicit Presentations

    Fix a simplicial map at common ambient sizes and explicit presentation
    choices at both ends. Reuse its existing class map between the two
    comparison maps; no proof that it preserves selected fillers is needed. *)

(** ** 映射显式呈现

    在共同环境大小处固定单纯映射及两端显式呈现选择。用两份比较映射夹住已有
    类映射，不要求该单纯映射保持所选填充。 *)

Section CylinderPresentationMaps.
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

(** The representative is the existing image triangle. The preservation
    proof may construct a new cylinder; it need not retain an input witness. *)

(** 代表是原有的像三角形；保相等证明可以构造新柱，不要求保留输入见证。 *)

Definition two_sphere_cylinder_map_resp
  : TwoSphereCylinderS X b KRX KCX →r
      TwoSphereCylinderS Y (α 0 b) KRY KCY
  := two_sphere_cylinder_of_class_resp Y (α 0 b) KRY KCY ∘r
      (two_sphere_class_map_resp α b ∘r
        two_sphere_class_of_cylinder_resp X b KRX KCX).

(** The comparison square commutes in the target's actual-cylinder
    equality. Its two paths retain the same image representative. *)

(** 比较方块按目标的实际柱相等交换；两条路径保留同一个像代表。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\operatorname{SphereClass}_2(X,b)
  \arrow[r,"\alpha_*"] \arrow[d,"I_X"'] &
\operatorname{SphereClass}_2(Y,\alpha_0b) \arrow[d,"I_Y"] \\
\operatorname{SphereCyl}_2(X,b) \arrow[r,"\alpha_*"'] &
\operatorname{SphereCyl}_2(Y,\alpha_0b)
\end{tikzcd}
\end{center}%
*)

Lemma two_sphere_cylinder_map_natural
  : (two_sphere_cylinder_map_resp ∘r
      two_sphere_cylinder_of_class_resp X b KRX KCX) ≈f
      (two_sphere_cylinder_of_class_resp Y (α 0 b) KRY KCY ∘r
        two_sphere_class_map_resp α b).
Proof.
  intros x. exact (TwoSphereConstantCylinder Y (α 0 b)
    (two_sphere_map_resp α b x) (two_sphere_map_resp α b x)
    (reflexivity (two_sphere_map_resp α b x))).
Defined.

End CylinderPresentationMaps.
