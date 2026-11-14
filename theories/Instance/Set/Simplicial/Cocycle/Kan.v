From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Four.
From Cats Require Import
  Algebra.Group.Cocycle.
From Cats.Set Require Import
  OrdinalAvoidance.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * From Actual Horns to Cocycle Fillers

    Low-dimensional horns have only vertices or edges to match. Higher
    horns retain the triangle labels and tetrahedron equations needed by
    sieve reconstruction. Membership witnesses keep the selected retained
    face; equality compares the underlying shape operator only.

    The proof uses
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Sieve.cocycle sieve universal}
    {%[cocycle_sieve_universal]%}% in the stable range, and
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Four.cocycle horn4 filler}
    {%[cocycle_horn4_filler]%}% at the critical fourth dimension.
    The final [two_cocycle_HasKanFillers] combines these with the lower
    dimensions, using the existing full [HasKanFillers] interface. *)

(** * 从实际 Horn 到 Cocycle 填充

    低维 horn 只需匹配顶点或边。高维 horn 保留筛重构所需的三角形标签与
    四面体方程。隶属见证保存选定的保留面，相等只比较底层形状算子。

    稳定范围使用
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Sieve.cocycle sieve universal}
    {%[cocycle_sieve_universal]%}%，关键的四维使用
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Four.cocycle horn4 filler}
    {%[cocycle_horn4_filler]%}%。最后的 [two_cocycle_HasKanFillers] 与
    更低维合并，使用已有的完整 [HasKanFillers] 接口。 *)

(** Any specified omitted vertex outside an operator's image gives actual
    horn membership, retaining a coface factorization. *)

(** 在算子像之外指定一个未被排除的顶点，保留余面分解即可得到实际 horn 隶属。 *)

Definition cocycle_horn_member_of_omission {m n : nat}
    (i j : Ordinal (S n)) (Hj : ¬ j = i)
    (f : (@Hom Δ) m (S n)) (H : ∀ a, ¬ f a = j)
  : f ∈Sv HornSieve (S n) i.
Proof.
  exists (j; Hj), (CofacePreimageF j f H).
  symmetry. apply coface_preimage_β.
Defined.

(** In dimensions at least four, avoid the missing vertex and all three
    triangle positions. Degenerate triangles are included. *)

(** 至少四维时，避开被排除顶点及三个三角形位置；其中也包括退化三角形。 *)

Definition cocycle_horn_triangle_member (n : nat)
    (i : Ordinal (S (S (S (S n)))))
    (f : (@Hom Δ) 2 (S (S (S (S n)))))
  : f ∈Sv HornSieve (S (S (S (S n)))) i.
Proof.
  destruct (fin_avoid_quadruple i (f fin_first)
    (f (fin_first⁺)) (f (fin_first⁺⁺)))
    as [j [Hi [H0 [H1 H2]]]].
  apply (cocycle_horn_member_of_omission i j Hi f).
  intros [[] | [[] | [[] | []]]] E;
    [apply H0 | apply H1 | apply H2]; symmetry; exact E.
Defined.

(** In dimensions at least five, the same argument retains every
    tetrahedron, including its degeneracies. *)

(** 至少五维时，同一论证保留每个四面体及其退化。 *)

Definition cocycle_horn_tetrahedron_member (n : nat)
    (i : Ordinal (S (S (S (S (S n))))))
    (f : (@Hom Δ) 3 (S (S (S (S (S n))))))
  : f ∈Sv HornSieve (S (S (S (S (S n))))) i.
Proof.
  destruct (fin_avoid_quintuple i (f fin_first)
    (f (fin_first⁺)) (f (fin_first⁺⁺))
    (f (fin_first⁺⁺⁺)))
    as [j [Hi [H0 [H1 [H2 H3]]]]].
  apply (cocycle_horn_member_of_omission i j Hi f).
  intros [[] | [[] | [[] | [[] | []]]]] E;
    [apply H0 | apply H1 | apply H2 | apply H3]; symmetry; exact E.
Defined.

(** ** The Small and Stable Ranges

    Fix the coefficient monoid and independent ambient value sizes.
    Neither the one- and two-dimensional fillers nor the stable range
    requires inverses or commutativity. *)

(** ** 最低维与稳定范围

    固定系数幺半群及独立环境值大小。一、二维填充及稳定范围均不要求逆或
    交换性。 *)

Section MonoidFillers.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}.

(** Every one-horn is filled by the unit edge, since all vertices agree. *)

(** 所有顶点相等，因此单位边填充每个一维 horn。 *)

Program Definition cocycle_horn1_HasFillers (i : Ordinal 1)
  : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 1 i
  :=
  {|horn_fill h := (two_cocycle_simplex_unit 1; _)
  |}.
Next Obligation.
  refine (snd (@horn_filler_faces_iff
    (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    0 i h (two_cocycle_simplex_unit 1)) _). intros j Hj.
  apply two_cocycle_zero_unique.
Defined.

(** All retained edges of a two-horn agree with those of the unit triangle. *)

(** 二维 horn 的全部保留边都与单位三角形的相应边相等。 *)

Program Definition cocycle_horn2_HasFillers (i : Ordinal 2)
  : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2 i
  :=
  {|horn_fill h := (two_cocycle_simplex_unit 2; _)
  |}.
Next Obligation.
  refine (snd (@horn_filler_faces_iff
    (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    1 i h (two_cocycle_simplex_unit 2)) _). intros j Hj.
  apply two_cocycle_one_unique.
Defined.

(** Every horn of dimension at least five has a unique filler, obtained
    from the general sieve reconstruction. This covers all degrees of its
    natural transformation, not only the generating faces. *)

(** 至少五维的每个 horn 均由一般筛重构得到唯一填充；结论覆盖自然变换的
    全部维度，不只覆盖生成面。 *)

Definition cocycle_higher_horn_universal (n : nat)
    (i : Ordinal (S (S (S (S (S n))))))
    (h : HornS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (S (S (S (S (S n))))) i)
  : ∃ x : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (S (S (S (S (S n))))),
      is_unique (R := carrier_equiv ((Z²(M) :
        Fct (Δ^op) SetCat@{u p _ _ _ _ _})
        (S (S (S (S (S n))))))) (is_horn_filler h) x
  := cocycle_sieve_universal (HornSieve _ i) h
      (cocycle_horn_triangle_member (S n) i)
      (cocycle_horn_tetrahedron_member n i).

(** Discarding the additional uniqueness proof in the stable range still
    retains its actual filler and full restriction equation. *)

(** 稳定范围中忘却额外唯一性证明，仍保留实际填充及完整限制方程。 *)

Program Definition cocycle_higher_HasFillers (n : nat)
    (i : Ordinal (S (S (S (S (S n))))))
  : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (S (S (S (S (S n))))) i
  :=
  {|horn_fill h := ((cocycle_higher_horn_universal n i h).1; _)
  |}.
Next Obligation.
  exact (@this _ _ _ _ _ (cocycle_higher_horn_universal n i h).2).
Defined.

End MonoidFillers.

(** ** Solving the Three-Dimensional Horn

    Fix a chosen group of coefficients. Read the three retained triangle
    coefficients from the actual horn map, solve for the missing fourth,
    and use triangle reconstruction to recover every retained face. This
    step does not assume commutativity. *)

(** ** 求解三维 Horn

    固定选定系数群。从实际 horn 映射读取三个保留三角形的系数，求出缺失的
    第四个系数，再用三角形重构恢复每个保留面。这一步不假设交换性。 *)

Section GroupFillers.
Universes u p.
Context {M : SetC} `{HG : !Group M}.

(** The selected coefficient solution gives a filler of the whole horn. *)

(** 选定的系数解给出整个 horn 的填充。 *)

Definition cocycle_horn3_filler (i : Ordinal 3)
    (h : HornS (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 i)
  : ∃ x : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3,
      is_horn_filler h x.
Proof.
  destruct i as [[] | [[] | [[] | [[] | []]]]].
  - assert (H1 : ¬ (fin_first⁺ : Ordinal 3) = fin_first)
      by discriminate.
    pose (c1 := two_cocycle_triangle_value_resp
      (face[fin_first; fin_first⁺; H1] h)).
    assert (H2 : ¬ (fin_first⁺⁺ : Ordinal 3) = fin_first)
      by discriminate.
    pose (c2 := two_cocycle_triangle_value_resp
      (face[fin_first; fin_first⁺⁺; H2] h)).
    assert (H3 : ¬ (fin_first⁺⁺⁺ : Ordinal 3) = fin_first)
      by discriminate.
    pose (c3 := two_cocycle_triangle_value_resp
      (face[fin_first; fin_first⁺⁺⁺; H3] h)).
    destruct (Cocycle123Solution c3 c1 c2) as [v Hv].
    exists {|lower := TetrahedronTwoCocycle c3 c1 v c2
      (@this _ _ _ _ _ Hv)
      |}.
    refine (snd (@horn_filler_faces_iff
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      2 _ h _) _). intros j Hj.
    destruct j as [[] | [[] | [[] | [[] | []]]]];
      try solve [destruct (Hj eq_refl)];
      apply cocycle_triangle_eq_of_value;
      first [exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H0 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H1 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H2 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H3 Hj h))].
  - assert (H0 : ¬ (fin_first : Ordinal 3) = fin_first⁺)
      by discriminate.
    pose (c0 := two_cocycle_triangle_value_resp
      (face[fin_first⁺; fin_first; H0] h)).
    assert (H2 : ¬ (fin_first⁺⁺ : Ordinal 3) = fin_first⁺)
      by discriminate.
    pose (c2 := two_cocycle_triangle_value_resp
      (face[fin_first⁺; fin_first⁺⁺; H2] h)).
    assert (H3 : ¬ (fin_first⁺⁺⁺ : Ordinal 3) = fin_first⁺)
      by discriminate.
    pose (c3 := two_cocycle_triangle_value_resp
      (face[fin_first⁺; fin_first⁺⁺⁺; H3] h)).
    destruct (Cocycle023Solution c3 c0 c2) as [v Hv].
    exists {|lower := TetrahedronTwoCocycle c3 v c0 c2
      (@this _ _ _ _ _ Hv)
      |}.
    refine (snd (@horn_filler_faces_iff
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      2 _ h _) _). intros j Hj.
    destruct j as [[] | [[] | [[] | [[] | []]]]];
      try solve [destruct (Hj eq_refl)];
      apply cocycle_triangle_eq_of_value;
      first [exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H0 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H1 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H2 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H3 Hj h))].
  - assert (H0 : ¬ (fin_first : Ordinal 3) = fin_first⁺⁺)
      by discriminate.
    pose (c0 := two_cocycle_triangle_value_resp
      (face[fin_first⁺⁺; fin_first; H0] h)).
    assert (H1 : ¬ (fin_first⁺ : Ordinal 3) = fin_first⁺⁺)
      by discriminate.
    pose (c1 := two_cocycle_triangle_value_resp
      (face[fin_first⁺⁺; fin_first⁺; H1] h)).
    assert (H3 : ¬ (fin_first⁺⁺⁺ : Ordinal 3) = fin_first⁺⁺)
      by discriminate.
    pose (c3 := two_cocycle_triangle_value_resp
      (face[fin_first⁺⁺; fin_first⁺⁺⁺; H3] h)).
    destruct (Cocycle013Solution c3 c1 c0) as [v Hv].
    exists {|lower := TetrahedronTwoCocycle c3 c1 c0 v
      (@this _ _ _ _ _ Hv)
      |}.
    refine (snd (@horn_filler_faces_iff
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      2 _ h _) _). intros j Hj.
    destruct j as [[] | [[] | [[] | [[] | []]]]];
      try solve [destruct (Hj eq_refl)];
      apply cocycle_triangle_eq_of_value;
      first [exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H0 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H1 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H2 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H3 Hj h))].
  - assert (H0 : ¬ (fin_first : Ordinal 3) = fin_first⁺⁺⁺)
      by discriminate.
    pose (c0 := two_cocycle_triangle_value_resp
      (face[fin_first⁺⁺⁺; fin_first; H0] h)).
    assert (H1 : ¬ (fin_first⁺ : Ordinal 3) = fin_first⁺⁺⁺)
      by discriminate.
    pose (c1 := two_cocycle_triangle_value_resp
      (face[fin_first⁺⁺⁺; fin_first⁺; H1] h)).
    assert (H2 : ¬ (fin_first⁺⁺ : Ordinal 3) = fin_first⁺⁺⁺)
      by discriminate.
    pose (c2 := two_cocycle_triangle_value_resp
      (face[fin_first⁺⁺⁺; fin_first⁺⁺; H2] h)).
    destruct (Cocycle012Solution c1 c0 c2) as [v Hv].
    exists {|lower := TetrahedronTwoCocycle v c1 c0 c2
      (@this _ _ _ _ _ Hv)
      |}.
    refine (snd (@horn_filler_faces_iff
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      2 _ h _) _). intros j Hj.
    destruct j as [[] | [[] | [[] | [[] | []]]]];
      try solve [destruct (Hj eq_refl)];
      apply cocycle_triangle_eq_of_value;
      first [exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H0 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H1 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H2 Hj h)) |
        exact (@func_proper _ _ two_cocycle_triangle_value_resp _ _
          (horn_face_witness_independent H3 Hj h))].
Defined.

End GroupFillers.

(** ** All Positive Dimensions

    Fix a chosen commutative group of coefficients and independent ambient
    value sizes. Combine the two unique low degrees, the three-dimensional
    coefficient solution, four-dimensional consistency, and the stable
    sieve reconstruction. No fillers are globally selected by import. *)

(** ** 全部正维度

    固定选定交换系数群及独立环境值大小。合并最低两维的唯一数据、三维系数
    求解、四维一致性与稳定范围的筛重构。导入模块不会全局选定填充结构。 *)

Section KanFilling.
Universes u p.
Context {M : SetC} `{HG : !Group M} `{HC : !IsCommutativeMonoid M}.

(** Retain the selected three-dimensional fillers as the existing interface. *)

(** 用已有接口保留选定的三维填充。 *)

Program Definition cocycle_horn3_HasFillers (i : Ordinal 3)
  : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 i
  :=
  {|horn_fill h := cocycle_horn3_filler i h
  |}.

(** Four-dimensional filling uses the actual retained triangles and the
    completed fifth equation. *)

(** 四维填充使用实际保留三角形及补出的第五条方程。 *)

Program Definition cocycle_horn4_HasFillers (i : Ordinal 4)
  : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 4 i
  :=
  {|horn_fill h := (CocycleHorn4Simplex i h
      (cocycle_horn_triangle_member 0 i); _)
  |}.
Next Obligation. apply cocycle_horn4_filler. Defined.

(** Every positive-dimensional inner or outer horn has a chosen filler.
    This is the full existing Kan interface, in specified setoid equality. *)

(** 每个正维内角或外角均有选定填充。这是在指定广集相等下的完整已有 Kan
    接口。 *)

Program Definition two_cocycle_HasKanFillers
  : HasKanFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  :=
  {|hasHornFillers n i := _
  |}.
Next Obligation.
  destruct n as [| [| [| [| n]]]].
  - exact (cocycle_horn1_HasFillers i).
  - exact (cocycle_horn2_HasFillers i).
  - exact (cocycle_horn3_HasFillers i).
  - exact (cocycle_horn4_HasFillers i).
  - exact (cocycle_higher_HasFillers n i).
Defined.

End KanFilling.
