From Cats Require Export
  Instance.Set.Simplicial.PrismOverlap
  Instance.Set.PresheafDescent.
From Cats Require Import
  Cat.Core.
From Cats.Set Require Import
  Pi
  Subset.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Gluing Values into a Product Cylinder

    The earlier
    %\coqref{Cats.Instance.Set.Simplicial.Prism.simplex prism eval factor}
    {%[simplex_prism_eval_factor]%}% reads a given map from its staircase
    values. We now construct a map from compatible supplied values.
    %\coqref{Cats.Instance.Set.PresheafDescent.PresheafDescendN}
    {%[PresheafDescendN]%}% does the descent: a cylinder element retains
    both spatial and time coordinates, and the computed prism factor
    places it in a maximal staircase. The dashed map is the result.
    The triangles commute in specified natural equality, not native
    equality of map or compatibility records. No Kan choices are needed. *)

(** * 将值粘成积柱映射

    前面的
    %\coqref{Cats.Instance.Set.Simplicial.Prism.simplex prism eval factor}
    {%[simplex_prism_eval_factor]%}% 从阶梯值读取给定映射。现在反过来，
    从给定相容值构造映射。一般下降
    %\coqref{Cats.Instance.Set.PresheafDescent.PresheafDescendN}
    {%[PresheafDescendN]%}% 承担粘合：柱元素保留空间及时间两个坐标，
    计算所得棱柱因子将它置于某块最大阶梯。虚线表示构造出的映射；三角形按
    指定自然相等交换，不比较映射或相容记录的原生相等，也不要求 Kan 选择。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
\Delta[m+1] \arrow[r,"{(\sigma_i,T_i)}"] \arrow[dr,"{\langle a_i\rangle}"']
  & \Delta[m]\times\Delta[1] \arrow[d,dashed,"{G}"]
  & \Delta[m+1] \arrow[l,"{(\sigma_j,T_j)}"']
    \arrow[dl,"{\langle a_j\rangle}"] \\
  & X &
\end{tikzcd}
\end{center}%
*)

(** One staircase generator has both actual coordinates. Its value sizes
    are explicitly the chosen carrier and equality bounds. *)

(** 一个阶梯生成元含两个实际坐标；其取值大小显式指定为所选载体与相等界。 *)

Definition simplex_prism_generator@{u p +} (m : nat) (i : Ordinal m)
  : SimplicialCylinderF
      (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S m)
  := ({|lower := σ[m; i]|}, {|lower := SimplexPrismTimeF i|}).

(** Every degree is covered, including degenerate simplices. The witness
    is the existing computed pivot and interleaved factor, not a new choice. *)

(** 每维均被覆盖，包括退化单形；见证就是已有计算枢轴与交织因子，无新选择。 *)

Definition simplex_prism_cover@{u p +} (m : nat)
  : is_presheaf_cover
      (Q := SimplicialCylinderF
        (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}))
      (simplex_prism_generator m).
Proof.
  intros n [[a] [t]]. destruct (SimplexPrismFactor a t) as [i [h [E F]]].
  exists i, h. split; refine {|lower := _|}; [exact E | exact F].
Defined.

(** ** Descent in Every Spatial Dimension

    Fix an arbitrary simplicial setoid at independent carrier/equality
    bounds and a spatial dimension. Compatibility compares all common
    spatial/time factors; no filling or algebra structure is present. *)

(** ** 每个空间维数上的下降

    固定载体与相等界独立的任意单纯广集及空间维数。相容性比较全部空间／时间
    共同因子；不引入填充或代数结构。 *)

Section PrismGluing.
Universes u p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {m : nat}.

Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialCylinderF (Δ[m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

Let e (i : Ordinal m)
  : Q (S m)
  := simplex_prism_generator m i.

(** The generic overlap equality is precisely the pair of spatial/time
    equations. Neither coordinate alone would suffice. *)

(** 一般交叠相等正是空间与时间两个方程；单个坐标不足。 *)

Definition simplex_prism_compatible_iff (a : Ordinal m → X (S m))
  : presheaf_values_compatible e a ↔
      (∀ n (i j : Ordinal m) (f g : (@Hom Δ) n (S m)),
        σ[m; i] ∘ f ≈ σ[m; j] ∘ g →
        SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g →
        X[f]Δ (a i) ≈S X[g]Δ (a j)).
Proof.
  split.
  - intros H n i j f g E F.
    apply (H n i j f g). split; refine {|lower := _|}; [exact E | exact F].
  - intros H n i j f g [[E] [F]]. exact (H n i j f g E F).
Defined.

(** Actual map values have the required compatibility by naturality. *)

(** 实际映射的值由自然性满足所需相容条件。 *)

Definition simplex_prism_values_compatible (K : Q ⇒ X)
  : presheaf_values_compatible e (λ i, simplex_prism_eval K i)
  := presheaf_map_values_compatible e K.

(** The cylinder map is the general descent for the computed cover. *)

(** 柱映射就是计算覆盖上的一般下降。 *)

Definition SimplexPrismGluingN (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible e a)
  : Q ⇒ X
  := PresheafDescendN e (simplex_prism_cover m) a H.

(** Reading the glued map recovers each supplied staircase value. *)

(** 读取粘合映射，恢复每块给定阶梯值。 *)

Lemma simplex_prism_gluing_β (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible e a) i
  : simplex_prism_eval (SimplexPrismGluingN a H) i ≈S a i.
Proof. exact (presheaf_descend_β e (simplex_prism_cover m) a H i). Defined.

(** Any supplied factor with both coordinate equations computes the value,
    regardless of the pivot chosen by the cover. *)

(** 任意满足两个坐标方程的给定因子都计算该值，不依赖覆盖所选枢轴。 *)

Lemma simplex_prism_gluing_factor (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible e a)
    {n : nat} (s : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
    (i : Ordinal m) (h : (@Hom Δ) n (S m))
    (E : σ[m; i] ∘ h ≈ s) (F : SimplexPrismTimeF i ∘ h ≈ t)
  : SimplexPrismGluingN a H n ({|lower := s|}, {|lower := t|}) ≈S
      X[h]Δ (a i).
Proof.
  apply (presheaf_descend_factor e (simplex_prism_cover m) a H
    n ({|lower := s|}, {|lower := t|}) i h).
  split; refine {|lower := _|}; [exact E | exact F].
Defined.

(** Gluing the values of an actual map recovers that whole map. *)

(** 粘合实际映射的值，恢复整个映射。 *)

Lemma simplex_prism_gluing_η (K : Q ⇒ X)
  : SimplexPrismGluingN (λ i, simplex_prism_eval K i)
      (simplex_prism_values_compatible K) ≈N K.
Proof. exact (presheaf_descend_η e (simplex_prism_cover m) K). Defined.

(** This is the full unique-extension property, reused from general
    descent rather than reproved degree by degree. *)

(** 这是完整的唯一延拓泛性质，复用一般下降，不逐维重证。 *)

Definition simplex_prism_gluing_universal (a : Ordinal m → X (S m))
    (H : presheaf_values_compatible e a)
  : is_unique (R := @NatEq _ _ _ _)
      (λ K : Q ⇒ X, ∀ i, simplex_prism_eval K i ≈S a i)
      (SimplexPrismGluingN a H)
  := presheaf_descend_universal e (simplex_prism_cover m) a H.

(** Equal values give equal glued maps even with different compatibility
    witnesses. No proof-field equality is needed. *)

(** 值相等则粘合映射相等，即使相容见证不同；不要求证明字段相等。 *)

Lemma simplex_prism_gluing_proper (a b : Ordinal m → X (S m))
    (H : presheaf_values_compatible e a)
    (K : presheaf_values_compatible e b) (E : ∀ i, a i ≈S b i)
  : SimplexPrismGluingN a H ≈N SimplexPrismGluingN b K.
Proof.
  exact (presheaf_descend_proper e (simplex_prism_cover m)
    (simplex_prism_cover m) a b H K E).
Defined.

(** A respectful map packages descent using the existing product/subset
    setoids; equality compares the values alone. *)

(** 用既有指标积／子集广集将下降打包成保相等映射，相等只比较值。 *)

Definition simplex_prism_gluing_resp
  : SubsetS (PiS (Ordinal m) (λ _, X (S m)))
      (presheaf_values_compatible e) →r Nat_SetS Q X
  := presheaf_descend_resp e (simplex_prism_cover m).

End PrismGluing.

(** ** Gluing Three Tetrahedra

    Fix three values and their two adjacent-face equations. The exact
    overlap criterion of
    %\coqref{Cats.Instance.Set.Simplicial.PrismOverlap.simplex triangle prism overlap iff}
    {%[simplex_triangle_prism_overlap_iff]%}% supplies every common-factor
    equation, including the first/last overlap through the middle piece.
    The general cylinder descent then gives existence and uniqueness. *)

(** ** 粘合三个四面体

    固定三个值及其两条相邻面方程。精确交叠判据
    %\coqref{Cats.Instance.Set.Simplicial.PrismOverlap.simplex triangle prism overlap iff}
    {%[simplex_triangle_prism_overlap_iff]%}% 提供全部共同因子方程，包括经
    中间块比较首尾交叠。然后由一般柱下降给出存在性和唯一性。 *)

Section TrianglePrismGluing.
Universes u p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (a : Ordinal 2 → X 3).
Context (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
  d[X; 2; fin_first⁺] (a fin_first⁺)).
Context (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
  d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺)).

(** The two equations provide precisely the generic compatibility used
    by descent; there is no new matching record. *)

(** 两条方程恰好提供下降所需的一般相容条件，不引入新匹配记录。 *)

Definition simplex_triangle_prism_values_compatible
  : presheaf_values_compatible (simplex_prism_generator 2) a
  := snd (simplex_prism_compatible_iff a)
      (λ n i j f g E F, simplex_triangle_prism_overlap a H0 H1 i j f g E F).

(** This is an actual map on the whole product cylinder, in every degree. *)

(** 这是整个积柱上的实际映射，定义于每一维。 *)

Definition SimplexTrianglePrismGluingN
  : SimplicialCylinderF
      (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X
  := SimplexPrismGluingN a simplex_triangle_prism_values_compatible.

(** Its three staircase values recover the supplied tetrahedra. *)

(** 三块阶梯处的值恢复给定四面体。 *)

Lemma simplex_triangle_prism_gluing_β (i : Ordinal 2)
  : simplex_prism_eval SimplexTrianglePrismGluingN i ≈S a i.
Proof. apply simplex_prism_gluing_β. Defined.

(** Uniqueness is the same general extension property. *)

(** 唯一性仍是同一个一般延拓泛性质。 *)

Definition simplex_triangle_prism_gluing_universal
  : is_unique (R := @NatEq _ _ _ _)
      (λ K : SimplicialCylinderF
        (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
        ∀ i, simplex_prism_eval K i ≈S a i) SimplexTrianglePrismGluingN
  := simplex_prism_gluing_universal a simplex_triangle_prism_values_compatible.

End TrianglePrismGluing.

(** Different values and adjacent-equation witnesses are compared only
    by pointwise specified equality of the values. *)

(** 不同值和相邻方程见证仅按值的逐点指定相等比较。 *)

Lemma simplex_triangle_prism_gluing_proper@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} (a b : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (K0 : d[X; 2; fin_first⁺] (b fin_first) ≈S
      d[X; 2; fin_first⁺] (b fin_first⁺))
    (K1 : d[X; 2; fin_first⁺⁺] (b fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (b fin_first⁺⁺))
    (E : ∀ i, a i ≈S b i)
  : SimplexTrianglePrismGluingN a H0 H1 ≈N
      SimplexTrianglePrismGluingN b K0 K1.
Proof. apply simplex_prism_gluing_proper. exact E. Defined.

(** Reading an actual triangle cylinder and gluing it back recovers the
    map, regardless of the derived compatibility proof. *)

(** 读取实际三角柱并重新粘合，恢复该映射，与所导出相容证明无关。 *)

Lemma simplex_triangle_prism_gluing_η@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (K : SimplicialCylinderF
      (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
  : SimplexTrianglePrismGluingN (λ i, simplex_prism_eval K i)
      (simplex_prism_values_adjacent K fin_first)
      (simplex_prism_values_adjacent K fin_first⁺) ≈N K.
Proof.
  transitivity (SimplexPrismGluingN (λ i, simplex_prism_eval K i)
    (simplex_prism_values_compatible K)).
  - apply simplex_prism_gluing_proper. intros i. reflexivity.
  - apply simplex_prism_gluing_η.
Defined.

(** The adjacent equations are necessary and sufficient for an actual
    cylinder map with these three specified values. This strengthens the
    previous compatibility criterion to gluing existence, without Kan. *)

(** 相邻方程是存在具有这三个指定值的实际柱映射的充要条件。这将先前的相容
    判据加强为粘合存在性，不使用 Kan。 *)

Definition simplex_triangle_prism_gluing_iff@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} (a : Ordinal 2 → X 3)
  : (∃ K : SimplicialCylinderF
        (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
        ∀ i, simplex_prism_eval K i ≈S a i) ↔
      (d[X; 2; fin_first⁺] (a fin_first) ≈S
        d[X; 2; fin_first⁺] (a fin_first⁺)) ∧
      (d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
        d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺)).
Proof.
  split.
  - intros [K E].
    assert (H : ∀ i : Ordinal 1,
      d[X; 2; i↑⁺] (a i↑) ≈S d[X; 2; i↑⁺] (a i⁺)).
    { intros i.
      transitivity (d[X; 2; i↑⁺] (simplex_prism_eval K i↑)).
      - apply func_proper. symmetry. exact (E i↑).
      - transitivity (d[X; 2; i↑⁺] (simplex_prism_eval K i⁺)).
        + apply simplex_prism_values_adjacent.
        + apply func_proper. exact (E i⁺). }
    exact (H fin_first, H fin_first⁺).
  - intros [H0 H1]. exists (SimplexTrianglePrismGluingN a H0 H1).
    apply simplex_triangle_prism_gluing_β.
Defined.
