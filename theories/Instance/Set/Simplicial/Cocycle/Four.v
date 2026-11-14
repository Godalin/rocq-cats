From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Finite
  Instance.Set.Simplicial.Cocycle.Sieve
  Instance.Set.Simplicial.Matching.
From Cats Require Import
  Algebra.Group.Cocycle
  Cat.Chain.

Local Open Scope monoid_scope.
Local Open Scope ordinal_scope.

(** * The Missing Tetrahedron Equation

    A four-dimensional horn retains all ten triangle labels and four of
    the five tetrahedron equations. Five-vertex consistency recovers the
    missing equation. This chapter connects that algebraic theorem to an
    actual horn map, whose naturality supplies all overlap comparisons.
    The coefficient argument is
    %\coqref{Cats.Algebra.Group.Cocycle.cocycle tetrahedron 1234}
    {%[cocycle_tetrahedron_1234]%}% and its four companion lemmas.

    Every triangle operator [θ] factors through this horn: there is a
    retained face avoiding its three positions and the excluded face index.
    The upper triangle commutes in shape-map equality. The dashed extension
    is constructed below; its restriction equation makes the lower triangle
    commute in natural-transformation equality. *)

(** * 缺失的四面体方程

    四维 horn 保留全部十个三角形标签及五条四面体方程中的四条。五顶点一致性
    恢复缺失方程。本章把该代数定理接到实际 horn 映射，自然性提供全部交叠
    比较。系数论证为
    %\coqref{Cats.Algebra.Group.Cocycle.cocycle tetrahedron 1234}
    {%[cocycle_tetrahedron_1234]%}% 及其四条伴随引理。

    每个三角形算子 [θ] 都经过该 horn 分解：总能找到一个保留面，避开它的
    三个位置及被排除的面索引。上方三角形按形状映射相等交换。下文构造虚线
    延拓，其限制方程使下方三角形按自然变换相等交换。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
 \Delta[2] \arrow[r,"{\widehat\theta}"] \arrow[dr,"\theta"'] &
 \Lambda[4;i] \arrow[d,"\iota"'] \arrow[dr,"h"] & \\
 & \Delta[4] \arrow[r,dashed,"{\langle x\rangle}"'] & Z^2(M)
\end{tikzcd}
\end{center}% *)

(** ** Ordering the Ten Coefficients

    Fix respectful triangle labels on [Ord 4] into a chosen monoid.
    A face equation can be written with the canonical ten coefficients
    irrespective of the order in which its two omitted positions are read. *)

(** ** 十个系数的次序

    固定到选定幺半群的 [Ord 4] 三角形保相等标签。无论按何种次序读取两个
    省略位置，每个面方程均可用规范的十个系数书写。 *)

Section FaceEquations.
Context {M : SetC} `{HM : !Monoid M}
    (t : (@Hom Δ) 2 4 → M)
    (t_proper : Proper (HomEq ==> carrier_equiv M) t).

(** Name the ten increasing triangles in the order [012], [013], [014],
    [023], [024], [034], [123], [124], [134], [234], as in
    [PentachoronLabel]. The coface formulas below select those positions. *)

(** 按 [PentachoronLabel] 的次序，为十个递增三角形 [012]、[013]、[014]、
    [023]、[024]、[034]、[123]、[124]、[134]、[234] 命名。
    下方余面公式选出这些位置。 *)

Let c_a
  : M
  := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]).
Let c_b
  : M
  := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]).
Let c_c
  : M
  := t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]).
Let c_d
  : M
  := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺]).
Let c_e
  : M
  := t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺]).
Let c_f
  : M
  := t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺]).
Let c_g
  : M
  := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first]).
Let c_h
  : M
  := t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first]).
Let c_i
  : M
  := t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first]).
Let c_j
  : M
  := t (δ[3; fin_first⁺] ∘F δ[2; fin_first]).

(** Normalize the selected tetrahedron equation to increasing triangles. *)

(** 将选定的四面体方程化为递增三角形的形式。 *)

Definition pentachoron_face_equation (j : Ordinal 4)
  : Type
  := match j with
     | inl _ => c_g ⋅ c_i ≈S c_j ⋅ c_h
     | inr (inl _) => c_d ⋅ c_f ≈S c_j ⋅ c_e
     | inr (inr (inl _)) => c_b ⋅ c_f ≈S c_i ⋅ c_c
     | inr (inr (inr (inl _))) => c_a ⋅ c_e ≈S c_h ⋅ c_c
     | inr (inr (inr (inr _))) => c_a ⋅ c_d ≈S c_g ⋅ c_b
     end.

(** Respect for equal shape maps identifies the two descriptions. *)

(** 保持相等形状映射，使两种描述相等。 *)

Lemma pentachoron_face_equation_iff (j : Ordinal 4)
  : (t (δ[3; j] ∘F δ[2; fin_first⁺⁺⁺]) ⋅
      t (δ[3; j] ∘F δ[2; fin_first⁺]) ≈S
     t (δ[3; j] ∘F δ[2; fin_first]) ⋅
      t (δ[3; j] ∘F δ[2; fin_first⁺⁺])) ↔
      pentachoron_face_equation j.
Proof.
  destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]];
    split; cbn [pentachoron_face_equation]; intros H.
  - transitivity ((t (δ[3; fin_first] ∘F δ[2; fin_first⁺⁺⁺])) ⋅
      (t (δ[3; fin_first] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first])) ⋅
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺] ∘F δ[2; fin_first⁺⁺⁺])) ⋅
      (t (δ[3; fin_first⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺])) ⋅
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺⁺⁺])) ⋅
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺])) ⋅
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺])) ⋅
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺])) ⋅
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺])) ⋅
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺])) ⋅
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺]))).
    + apply monoid_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
    + transitivity ((t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first])) ⋅
        (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))).
      * exact H.
      * apply monoid_mul_proper; apply t_proper;
          apply (snd (simplex_eq_iff _ _));
          intros [[] | [[] | [[] | []]]]; reflexivity.
Defined.

End FaceEquations.

(** ** Completing the Five Face Equations

    Fix a chosen commutative coefficient group. Four face equations imply
    the fifth by the integrated five-vertex consistency theorem. The index
    of the missing face is finite, so this is a transparent five-case choice. *)

(** ** 补全五个面方程

    固定选定交换系数群。由已集成的五顶点一致性，四个面方程推出第五个。
    缺失面索引有限，因此这是透明的五种情形选择。 *)

Section CompletingEquations.
Context {M : SetC} `{HG : !Group M} `{HC : !IsCommutativeMonoid M}
    (t : (@Hom Δ) 2 4 → M).
(** Retain every equation, including the missing one. *)

(** 保留每条方程，包括缺失的一条。 *)

Lemma pentachoron_complete_equations (i : Ordinal 4)
    (H : ∀ j, (¬ j = i) → pentachoron_face_equation t j)
  : ∀ j, pentachoron_face_equation t j.
Proof.
  pose (c_a := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺])).
  pose (c_b := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺])).
  pose (c_c := t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺])).
  pose (c_d := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺])).
  pose (c_e := t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺])).
  pose (c_f := t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺])).
  pose (c_g := t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first])).
  pose (c_h := t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first])).
  pose (c_i := t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first])).
  pose (c_j := t (δ[3; fin_first⁺] ∘F δ[2; fin_first])).
  destruct i as [[] | [[] | [[] | [[] | [[] | []]]]]].
  - assert (E1 : pentachoron_face_equation t fin_first⁺).
    { apply H. discriminate. }
    assert (E2 : pentachoron_face_equation t fin_first⁺⁺).
    { apply H. discriminate. }
    assert (E3 : pentachoron_face_equation t fin_first⁺⁺⁺).
    { apply H. discriminate. }
    assert (E4 : pentachoron_face_equation t fin_first⁺⁺⁺⁺).
    { apply H. discriminate. }
    intros j. destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]].
    + exact (cocycle_tetrahedron_1234 c_a c_b c_c c_d c_e c_f c_g c_h c_i c_j
        E1 E2 E3 E4).
    + exact E1.
    + exact E2.
    + exact E3.
    + exact E4.
  - assert (E0 : pentachoron_face_equation t fin_first).
    { apply H. discriminate. }
    assert (E2 : pentachoron_face_equation t fin_first⁺⁺).
    { apply H. discriminate. }
    assert (E3 : pentachoron_face_equation t fin_first⁺⁺⁺).
    { apply H. discriminate. }
    assert (E4 : pentachoron_face_equation t fin_first⁺⁺⁺⁺).
    { apply H. discriminate. }
    intros j. destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]].
    + exact E0.
    + exact (cocycle_tetrahedron_0234 c_a c_b c_c c_d c_e c_f c_g c_h c_i c_j
        E0 E2 E3 E4).
    + exact E2.
    + exact E3.
    + exact E4.
  - assert (E0 : pentachoron_face_equation t fin_first).
    { apply H. discriminate. }
    assert (E1 : pentachoron_face_equation t fin_first⁺).
    { apply H. discriminate. }
    assert (E3 : pentachoron_face_equation t fin_first⁺⁺⁺).
    { apply H. discriminate. }
    assert (E4 : pentachoron_face_equation t fin_first⁺⁺⁺⁺).
    { apply H. discriminate. }
    intros j. destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]].
    + exact E0.
    + exact E1.
    + exact (cocycle_tetrahedron_0134 c_a c_b c_c c_d c_e c_f c_g c_h c_i c_j
        E0 E1 E3 E4).
    + exact E3.
    + exact E4.
  - assert (E0 : pentachoron_face_equation t fin_first).
    { apply H. discriminate. }
    assert (E1 : pentachoron_face_equation t fin_first⁺).
    { apply H. discriminate. }
    assert (E2 : pentachoron_face_equation t fin_first⁺⁺).
    { apply H. discriminate. }
    assert (E4 : pentachoron_face_equation t fin_first⁺⁺⁺⁺).
    { apply H. discriminate. }
    intros j. destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]].
    + exact E0.
    + exact E1.
    + exact E2.
    + exact (cocycle_tetrahedron_0124 c_a c_b c_c c_d c_e c_f c_g c_h c_i c_j
        E0 E1 E2 E4).
    + exact E4.
  - assert (E0 : pentachoron_face_equation t fin_first).
    { apply H. discriminate. }
    assert (E1 : pentachoron_face_equation t fin_first⁺).
    { apply H. discriminate. }
    assert (E2 : pentachoron_face_equation t fin_first⁺⁺).
    { apply H. discriminate. }
    assert (E3 : pentachoron_face_equation t fin_first⁺⁺⁺).
    { apply H. discriminate. }
    intros j. destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]].
    + exact E0.
    + exact E1.
    + exact E2.
    + exact E3.
    + exact (cocycle_tetrahedron_0123 c_a c_b c_c c_d c_e c_f c_g c_h c_i c_j
        E0 E1 E2 E3).
Defined.

End CompletingEquations.

(** ** Reconstructing the Actual Four-Horn

    Fix a chosen commutative coefficient group, independent ambient value
    sizes, a missing face and an actual horn map. Read triangle labels from
    the map. Its retained face values supply the four given equations;
    the completion theorem supplies the fifth. *)

(** ** 重构实际四维 Horn

    固定选定交换系数群、独立环境值大小、缺失面及实际 horn 映射。从映射读取
    三角形标签，保留面的值提供四条已知方程，补全定理提供第五条。 *)

Section ActualFourHorn.
Universes u p.
Context {M : SetC} `{HG : !Group M} `{HC : !IsCommutativeMonoid M}
    (i : Ordinal 4)
    (h : HornS (Z²(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 4 i)
    (T : ∀ f : (@Hom Δ) 2 4, f ∈Sv HornSieve 4 i).

Let t (f : (@Hom Δ) 2 4)
  : M
  := cocycle_sieve_triangle (HornSieve 4 i) h T f.

(** Naturality supplies each retained tetrahedron equation in the canonical
    coefficient ordering. *)

(** 自然性以规范系数次序提供每个保留四面体的方程。 *)

Lemma cocycle_horn4_face_equation (j : Ordinal 4) (Hj : ¬ j = i)
  : pentachoron_face_equation t j.
Proof.
  apply (fst (pentachoron_face_equation_iff t
    (cocycle_sieve_triangle_proper (HornSieve 4 i) h T) j)).
  exact (cocycle_sieve_triangle_tetrahedron (HornSieve 4 i) h T
    δ[3; j] (horn_face_member i j Hj)).
Defined.

(** The completed table is an actual four-simplex in the original value
    universes. Only coefficient labels are compared, never law fields. *)

(** 补全标签表是原值宇宙中的实际四维单形；只比较系数标签，不比较定律字段。 *)

Definition CocycleHorn4Simplex
  : (Z²(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 4
  :=
  {|lower := PentachoronTwoCocycle
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]))
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺⁺]))
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺]))
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first⁺]))
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first⁺]))
      (t (δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first]))
      (t (δ[3; fin_first⁺⁺⁺] ∘F δ[2; fin_first]))
      (t (δ[3; fin_first⁺⁺] ∘F δ[2; fin_first]))
      (t (δ[3; fin_first⁺] ∘F δ[2; fin_first]))
      (pentachoron_complete_equations t i cocycle_horn4_face_equation
        fin_first)
      (pentachoron_complete_equations t i cocycle_horn4_face_equation
        fin_first⁺)
      (pentachoron_complete_equations t i cocycle_horn4_face_equation
        fin_first⁺⁺)
      (pentachoron_complete_equations t i cocycle_horn4_face_equation
        fin_first⁺⁺⁺)
      (pentachoron_complete_equations t i cocycle_horn4_face_equation
        fin_first⁺⁺⁺⁺)
  |}.

(** Every triangle of every retained simplex is recovered by naturality,
    proving equality with the full horn map. *)

(** 自然性恢复每个保留单形的每个三角形，因而证明与完整 horn 映射相等。 *)

Lemma cocycle_horn4_filler
  : is_horn_filler h CocycleHorn4Simplex.
Proof.
  intros m [[f H]]. refine {|lower := _
                          |}.
  intros x y z g k.
  transitivity (t (f ∘F ⟦⟨g, k⟩Ch⟧Ch)).
  - exact (pentachoron_label_read t
      (cocycle_sieve_triangle_proper (HornSieve 4 i) h T)
      (cocycle_sieve_triangle_unit (HornSieve 4 i) h T)
      (f ∘F ⟦⟨g, k⟩Ch⟧Ch)).
  - apply cocycle_sieve_triangle_value.
Defined.

End ActualFourHorn.
