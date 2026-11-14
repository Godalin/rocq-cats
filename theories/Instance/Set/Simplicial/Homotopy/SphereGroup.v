From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereAssociativity
  Algebra.Group.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Group on the Existing Sphere Class Setoid

    The preceding constructions supplied a respectful multiplication,
    associativity, the constant unit and separate left/right inverse
    candidates with actual tetrahedron witnesses. We now assemble the
    existing [Semigroup], [Monoid] and [Group] interfaces. Every parent
    retains exactly the already selected multiplication and equality.

    The key algebraic step is already available as
    %\coqref{Cats.Algebra.Monoid.Core.monoid_inverse_unique}
    {%[monoid_inverse_unique]%}%: a left and a right inverse agree. Apply
    it to the two candidates, then choose the left one as the group
    inverse. The right inverse law follows by that agreement. Generic
    [group_inv_proper], [group_inv_unique] and [group_inv_resp] now apply;
    none of their algebraic proofs is rebuilt for spheres.

    All selections stay explicit. In the diagram I_L and I_R denote
    independently supplied left/right candidates. The square expresses
    the inverse agreement needed to read a right inverse law for I_L.
    No equality of tetrahedra, functions or structure records is asserted.
    This is a group on the simplex presentation of sphere classes;
    commutativity, general π₂ identification, cylinder/path comparison and
    weak-equivalence invariants remain further work. The next chapter's
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_map_mul}
    {%[two_sphere_class_map_mul]%}% connects the existing simplicial class
    maps to this selected multiplication, without assuming that maps
    preserve chosen fillers. *)

(** * 既有球面类广集上的群

    前面的构造已给出保相等乘法、结合律、常值单位，以及带实际四面体见证的
    独立左右逆候选。现在组装既有 [Semigroup]、[Monoid]、[Group] 接口，
    每个父结构都保留完全相同的已选乘法及相等。

    关键代数步骤已经由
    %\coqref{Cats.Algebra.Monoid.Core.monoid_inverse_unique}
    {%[monoid_inverse_unique]%}% 给出：左逆与右逆相等。将它应用于两个候选，
    再选左候选为群逆；由候选相等得到右逆律。一般 [group_inv_proper]、
    [group_inv_unique]、[group_inv_resp] 随即适用，不为球面重做代数证明。

    所有选择仍须显式给出。下图 I_L、I_R 表示独立给定的左右候选；方块表示
    将 I_L 读作右逆所需的逆相等。不等同四面体、函数或结构记录。这是在球面类
    的单形呈现上构造的群；交换性、一般 π₂ 识别、柱／路径比较和弱等价不变量
    仍需进一步工作。下一章的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroupMap.two_sphere_class_map_mul}
    {%[two_sphere_class_map_mul]%}% 将既有单纯类映射与此选定乘法接通，
    不假设映射保持选定填充。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
(x,I_Lx) \arrow[r,"{\mathrm{id},\ I_Lx\approx I_Rx}"]
  \arrow[d,"\mu"'] & (x,I_Rx) \arrow[d,"\mu"] \\
b_2 \arrow[r,equal] & b_2
\end{tikzcd}
\qquad $I_Lx\cdot x\approx b_2,\quad x\cdot I_Rx\approx b_2.$
\end{center}%
*)

(** ** The Same Selected Parents and Explicit Inverse Choices

    Fix independent simplex carrier/equality sizes, a base vertex and
    only the three dimension-four selections needed for class descent
    and associativity. Multiplication selects dimension-three missing face
    two; inverse candidates independently select missing faces three/one.
    Full Kan, respectful selection and filler uniqueness are not assumed. *)

(** ** 相同选定父结构与显式逆选择

    固定独立单形载体／相等大小、基点及类下降和结合律所需的三个四维选择。
    乘法选择三维缺第二面；逆候选独立选择缺第三／第一面。不假设完整 Kan、
    选择保相等或填充唯一性。 *)

Section SphereClassGroup.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.

Let Q
  : SetC
  := TwoSphereClassS X b.

(** Add only associativity to the already chosen class magma. *)

(** 只为已选类原群增加结合律。 *)

Program Definition TwoSphereClassSemigroup
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Semigroup Q
  :=
  {|SemigroupM := TwoSphereClassMagma X b H
  ; semigroup_assoc := two_sphere_kan_mul_assoc X b H
  |}.

(** Keep that same semigroup and the actual constant sphere as unit. *)

(** 保留同一个半群，并以实际常值球面为单位。 *)

Program Definition TwoSphereClassMonoid
    (H : HasHornFillers X 3 fin_first⁺⁺)
  : Monoid Q
  :=
  {|MonoidSG := TwoSphereClassSemigroup H
  ; monoid_unit := two_sphere_base X b
  ; monoid_unit_l := two_sphere_kan_mul_unit_l X b H
  ; monoid_unit_r := two_sphere_kan_mul_unit_r X b H
  |}.

(** General monoid inverse uniqueness identifies the two independent
    candidates in generated class equality, not as tetrahedron records. *)

(** 一般幺半群逆唯一性按生成类相等识别两个独立候选，不等同四面体记录。 *)

Lemma two_sphere_inverse_candidates_eq
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺) (x : Q)
  : ((@SphereKanLeftInverse X b K x).1 : Q) ≈S
      (@SphereKanRightInverse X b L x).1.
Proof.
  exact (@monoid_inverse_unique Q (TwoSphereClassMonoid H) x
    (@SphereKanLeftInverse X b K x).1 (@SphereKanRightInverse X b L x).1
    (two_sphere_kan_mul_inverse_l X b H K x)
    (two_sphere_kan_mul_inverse_r X b H L x)).
Defined.

(** Choose the actual left candidate as inverse on the very same monoid.
    The right law uses candidate agreement and the existing right witness.
    Importing this value selects no model instance. *)

(** 在完全相同的幺半群上，选实际左候选为逆。右逆律使用候选相等及既有右见证；
    导入此值不选择模型实例。 *)

Program Definition TwoSphereClassGroup
    (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺)
  : Group Q
  :=
  {|GroupM := TwoSphereClassMonoid H
  ; group_inv x := (@SphereKanLeftInverse X b K x).1
  ; group_inv_l := two_sphere_kan_mul_inverse_l X b H K
  |}.
Next Obligation.
  transitivity (two_sphere_kan_mul X b H x
    (@SphereKanRightInverse X b L x).1).
  - exact (two_sphere_kan_mul_proper X b H x x (reflexivity x)
      _ _ (two_sphere_inverse_candidates_eq H K L x)).
  - exact (two_sphere_kan_mul_inverse_r X b H L x).
Defined.

(** Independent multiplication and left/right candidate choices induce
    pointwise equal respectful inverse maps. Reuse general group inverse
    uniqueness after comparing the two selected multiplications. *)

(** 独立乘法及左右候选选择给出逐点相等的保相等逆映射。在比较两份选定乘法后，
    复用一般群逆唯一性。 *)

Lemma two_sphere_class_group_inverse_choice_eq
    (H H' : HasHornFillers X 3 fin_first⁺⁺)
    (K K' : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L L' : HasHornFillers X 3 fin_first⁺)
  : @group_inv_resp Q (TwoSphereClassGroup H K L) ≈f
      @group_inv_resp Q (TwoSphereClassGroup H' K' L').
Proof.
  intros x. refine (@group_inv_unique Q (TwoSphereClassGroup H' K' L') x
    (@group_inv Q (TwoSphereClassGroup H K L) x) _).
  transitivity (two_sphere_kan_mul X b H
    (@group_inv Q (TwoSphereClassGroup H K L) x) x).
  - exact (two_sphere_kan_composite_choice_eq X b H' H _ x).
  - exact (@group_inv_l Q (TwoSphereClassGroup H K L) x).
Defined.

End SphereClassGroup.
