From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Low
  Instance.Set.Sieve.Core.
From Cats Require Import
  Cat.Chain
  Instance.Nat.Order.
From Stdlib Require Import
  Lia.

Local Open Scope monoid_scope.
Local Open Scope ordinal_scope.

(** * Reconstructing Cocycles from Triangle Restrictions

    Fix a coefficient monoid. A label for every ordered triangle determines
    a cocycle if repeated positions have unit label and every ordered
    tetrahedron satisfies the cocycle equation. This reconstruction will
    let actual sieve maps, including horns, supply the local labels. *)

(** * 从三角形限制重构 Cocycle

    固定系数幺半群。每个有序三角形的标签若在重复位置时取单位，并在每个
    有序四面体上满足 cocycle 方程，就确定一个 cocycle。这个重构让包括
    horn 在内的实际筛映射提供局部标签。 *)

(** The four ordered endpoints of three composable arrows give a shape
    operator. Its arrow action is the thin ordinal action. *)

(** 三条可复合箭头的四个有序端点给出形状算子；箭头作用采用薄序数作用。 *)

Program Definition cocycle_tetrahedron_shape {n : nat}
    {x y z w : Ordinal n}
    (f : (@Hom [Ord n]) x y) (g : (@Hom [Ord n]) y z)
    (h : (@Hom [Ord n]) z w)
  : (@Hom Δ) 3 n
  := OrdinalF (λ a : Ordinal 3, match a with
      | inl _ => x
      | inr (inl _) => y
      | inr (inr (inl _)) => z
      | inr (inr (inr _)) => w
      end) _.
Next Obligation.
  pose proof (@nat_le_to_le _ _ f).
  pose proof (@nat_le_to_le _ _ g).
  pose proof (@nat_le_to_le _ _ h).
  destruct x0 as [[] | [[] | [[] | [[] | []]]]],
    y0 as [[] | [[] | [[] | [[] | []]]]]; cbn in *; lia.
Defined.

(** ** Label Reconstruction

    Fix an ordinal and labels respectful in the equality of shape maps.
    The two normalization hypotheses cover both repeated positions. *)

(** ** 标签重构

    固定序数及保持形状映射相等的标签。两条归一化假设分别覆盖两种重复位置。 *)

Section Reconstruction.
Context {M : SetC} `{HM : !Monoid M} {n : nat}
    (t : (@Hom Δ) 2 n → M)
    (t_proper : Proper (HomEq ==> carrier_equiv M) t)
    (t_unit : ∀ (f : (@Hom Δ) 1%nat n) (i : Ordinal 1%nat),
      t (f ∘F σ[1; i]) ≈S 1)
    (t_tetrahedron : ∀ f : (@Hom Δ) 3 n,
      t (f ∘F δ[2; fin_first⁺⁺⁺]) ⋅
        t (f ∘F δ[2; fin_first⁺]) ≈S
      t (f ∘F δ[2; fin_first]) ⋅
        t (f ∘F δ[2; fin_first⁺⁺])).

Local Existing Instance t_proper.

(** Read the label at the shape of each composable pair. *)

(** 在每一对可复合箭头的形状处读取标签。 *)

Program Definition TriangleLabelCocycle
  : TwoCocycle [Ord n] M
  :=
  {|two_cocycle_triangle x y z f g := t (⟦⟨f, g⟩Ch⟧Ch)
  |}.
Next Obligation.
  intros f f' Hf g g' Hg. apply t_proper.
  apply (snd (simplex_eq_iff _ _)).
  intros [[] | [[] | [[] | []]]]; reflexivity.
Defined.
Next Obligation.
  transitivity (t (⟦ArrowChain (C := [Ord n]) f⟧Ch ∘F σ[1; fin_first])).
  - apply t_proper. apply (snd (simplex_eq_iff _ _)).
    intros [[] | [[] | [[] | []]]]; reflexivity.
  - apply t_unit.
Defined.
Next Obligation.
  transitivity (t (⟦ArrowChain (C := [Ord n]) f⟧Ch ∘F σ[1; fin_first⁺])).
  - apply t_proper. apply (snd (simplex_eq_iff _ _)).
    intros [[] | [[] | [[] | []]]]; reflexivity.
  - apply t_unit.
Defined.
Next Obligation.
  pose (Q := cocycle_tetrahedron_shape f g h).
  transitivity
    (t (Q ∘F δ[2; fin_first⁺⁺⁺]) ⋅
      t (Q ∘F δ[2; fin_first⁺])).
  - apply magma_mul_proper; apply t_proper;
      apply (snd (simplex_eq_iff _ _));
      intros [[] | [[] | [[] | []]]]; reflexivity.
  - transitivity (t (Q ∘F δ[2; fin_first]) ⋅
      t (Q ∘F δ[2; fin_first⁺⁺])).
    + apply t_tetrahedron.
    + apply magma_mul_proper; apply t_proper;
        apply (snd (simplex_eq_iff _ _));
        intros [[] | [[] | [[] | []]]]; reflexivity.
Defined.

End Reconstruction.

(** ** Values of an Actual Sieve Map

    Fix a sieve and a map into the cocycle model. Naturality compares
    restriction with evaluation on a composite; membership witnesses are
    retained but never identified. In the square, [R_m] means the degree-m
    setoid of the realized sieve. For a triangle operator [θ], the two
    routes to [Z²(M) 2] agree in specified equality. Evaluation at its
    increasing triangle then gives the coefficient in [M]. This is the
    compatibility used by [cocycle_sieve_triangle_value]. *)

(** ** 实际筛映射的值

    固定筛及到 cocycle 模型的映射。自然性比较限制与在复合处求值；隶属见证
    保留为数据，但不等同这些见证。图中 [R_m] 表示实现后筛的 m 维广集。
    对三角形算子 [θ]，到 [Z²(M) 2] 的两条路线按指定相等一致，再在递增
    三角形处求值，得到 [M] 中的系数。这就是
    [cocycle_sieve_triangle_value] 使用的相容性。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
 R_m \arrow[r,"b_m"] \arrow[d,"{R[\theta]}"'] &
 Z^2(M)_m \arrow[d,"{\theta^*}"] & \\
 R_2 \arrow[r,"b_2"'] & Z^2(M)_2 \arrow[r,"{\mathrm{ev}_{012}}"'] & M
\end{tikzcd}
\end{center}% *)

Section SieveValues.
Universes u p.
Context {M : SetC} `{HM : !Monoid M} {n : nat} (R : Sieve Δ n)
    (b : SievePsh R ⇒ (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})).

(** Evaluate at a member with its explicit factorization witness. *)

(** 在成员处使用其显式分解见证求值。 *)

Definition cocycle_sieve_value {m : nat} (f : (@Hom Δ) m n)
    (H : f ∈Sv R)
  : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) m
  := b m {|lower := (f; H)
          |}.

(** All equal factorizations give equal restricted values. *)

(** 相等的分解均给出相等的限制值。 *)

Lemma cocycle_sieve_value_restrict {m k : nat}
    (f : (@Hom Δ) m n) (H : f ∈Sv R)
    (θ : (@Hom Δ) k m) (g : (@Hom Δ) k n) (K : g ∈Sv R)
    (E : f ∘F θ ≅N g)
  : Z²(M)[θ]Δ (cocycle_sieve_value f H) ≈S cocycle_sieve_value g K.
Proof.
  transitivity (b k (fmap (SievePsh R) θ {|lower := (f; H)
                                        |})).
  - symmetry. apply (nt_naturality b θ).
  - apply func_proper. exact {|lower := E
                             |}.
Defined.

Context (T : ∀ f : (@Hom Δ) 2 n, f ∈Sv R).

(** Read the increasing triangle of the value at each triangle operator. *)

(** 读取每个三角形算子处的值所包含的递增三角形标签。 *)

Definition cocycle_sieve_triangle (f : (@Hom Δ) 2 n)
  : M
  := two_cocycle_triangle_value_resp (cocycle_sieve_value f (T f)).

(** The chosen membership proof has no effect on coefficient equality. *)

(** 选定的隶属证明不影响系数相等。 *)

Global Instance cocycle_sieve_triangle_proper
  : Proper (HomEq ==> carrier_equiv M) cocycle_sieve_triangle.
Proof.
  intros f g E. apply func_proper. apply func_proper.
  exact {|lower := E
         |}.
Defined.

(** Restricting a local cocycle to a triangle reads its existing label. *)

(** 将局部 cocycle 限制到三角形，读出的就是其已有标签。 *)

Lemma cocycle_sieve_triangle_value {m : nat}
    (f : (@Hom Δ) m n) (H : f ∈Sv R)
    {x y z : Ordinal m}
    (g : (@Hom [Ord m]) x y) (h : (@Hom [Ord m]) y z)
  : cocycle_sieve_triangle (f ∘F ⟦⟨g, h⟩Ch⟧Ch) ≈S
      (lower (cocycle_sieve_value f H))⟦g, h⟧₂.
Proof.
  unfold cocycle_sieve_triangle.
  transitivity (two_cocycle_triangle_value_resp
    (Z²(M)[⟦⟨g, h⟩Ch⟧Ch]Δ (cocycle_sieve_value f H))).
  - apply func_proper. symmetry.
    apply cocycle_sieve_value_restrict. reflexivity.
  - cbn. apply two_cocycle_triangle_proper; exact tt.
Defined.

(** Reading a triangle commutes with any retained restriction. *)

(** 读取三角形与任意保留限制交换。 *)

Lemma cocycle_sieve_triangle_restrict {m : nat}
    (f : (@Hom Δ) m n) (H : f ∈Sv R) (θ : (@Hom Δ) 2 m)
  : cocycle_sieve_triangle (f ∘F θ) ≈S
      two_cocycle_triangle_value_resp
        (Z²(M)[θ]Δ (cocycle_sieve_value f H)).
Proof.
  apply func_proper. symmetry.
  apply cocycle_sieve_value_restrict. reflexivity.
Defined.

(** Triangle coverage also supplies an edge through its split degeneracy. *)

(** 三角形覆盖也经由可分裂的退化提供边的隶属见证。 *)

Definition cocycle_sieve_edge_member (f : (@Hom Δ) 1%nat n)
  : f ∈Sv R.
Proof.
  pose (Q := f ∘F σ[1; fin_first]).
  assert (E : Q ∘F δ[1; fin_first] ≅N f).
  { apply (snd (simplex_eq_iff _ _)).
    intros [[] | [[] | []]]; reflexivity. }
  apply (fst (@sieve_member_proper Δ n R 1%nat _ _ E)).
  exact (sieve_precomp R Q δ[1; fin_first] (T Q)).
Defined.

(** The coefficient of every repeated-position triangle is the unit. *)

(** 每个重复位置三角形的系数均为单位。 *)

Lemma cocycle_sieve_triangle_unit (f : (@Hom Δ) 1%nat n)
    (i : Ordinal 1%nat)
  : cocycle_sieve_triangle (f ∘F σ[1; i]) ≈S 1.
Proof.
  transitivity (two_cocycle_triangle_value_resp
    (Z²(M)[σ[1; i]]Δ
      (cocycle_sieve_value f (cocycle_sieve_edge_member f)))).
  - apply cocycle_sieve_triangle_restrict.
  - transitivity (two_cocycle_triangle_value_resp
      (two_cocycle_simplex_unit 2)).
    + apply func_proper. apply two_cocycle_degenerate_one.
    + reflexivity.
Defined.

(** Naturality reduces the four global triangle labels to one retained
    tetrahedron, where the original cocycle law applies. *)

(** 自然性将四个全局三角形标签化到一个保留四面体上，再应用原 cocycle 律。 *)

Lemma cocycle_sieve_triangle_tetrahedron (f : (@Hom Δ) 3 n)
    (H : f ∈Sv R)
  : cocycle_sieve_triangle
      (f ∘F δ[2; fin_first⁺⁺⁺]) ⋅
      cocycle_sieve_triangle (f ∘F δ[2; fin_first⁺]) ≈S
    cocycle_sieve_triangle (f ∘F δ[2; fin_first]) ⋅
      cocycle_sieve_triangle (f ∘F δ[2; fin_first⁺⁺]).
Proof.
  pose (c := lower (cocycle_sieve_value f H)).
  pose (a := ordinal_step (n := 3) fin_first).
  pose (d := ordinal_step (n := 3) (fin_next (fin_first))).
  pose (e := ordinal_step (n := 3) (fin_next (fin_next (fin_first)))).
  transitivity (c⟦a, d⟧₂ ⋅ c⟦d ∘ a, e⟧₂).
  - apply magma_mul_proper;
      (etransitivity; [apply cocycle_sieve_triangle_restrict |]);
      cbn; apply two_cocycle_triangle_proper; exact tt.
  - transitivity (c⟦d, e⟧₂ ⋅ c⟦a, e ∘ d⟧₂).
    + apply two_cocycle_tetrahedron.
    + apply magma_mul_proper; symmetry;
        (etransitivity; [apply cocycle_sieve_triangle_restrict |]);
        cbn; apply two_cocycle_triangle_proper; exact tt.
Defined.

Context (U : ∀ f : (@Hom Δ) 3 n, f ∈Sv R).

(** Reconstruct the actual simplex from a sieve containing all triangles
    and tetrahedra. Its coefficient monoid need not be a group. *)

(** 从包含全部三角形与四面体的筛重构实际单形；系数幺半群无须为群。 *)

Definition CocycleSieveSimplex
  : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n
  :=
  {|lower := TriangleLabelCocycle cocycle_sieve_triangle
      cocycle_sieve_triangle_proper cocycle_sieve_triangle_unit
      (λ f, cocycle_sieve_triangle_tetrahedron f (U f))
  |}.

(** Every local label agrees with the reconstructed global label, so the
    entire map from the sieve is recovered, in every degree. *)

(** 每个局部标签都与重构的全局标签相等，故恢复全部维度上的整个筛映射。 *)

Lemma cocycle_sieve_filler
  : CocycleSieveSimplex↾Sv[Z²(M); R] ≈N b.
Proof.
  intros m [[f H]]. refine {|lower := _
                          |}.
  intros x y z g h.
  transitivity (cocycle_sieve_triangle (f ∘F ⟦⟨g, h⟩Ch⟧Ch)).
  - apply cocycle_sieve_triangle_proper.
    apply (snd (simplex_eq_iff _ _)).
    intros [[] | [[] | [[] | []]]]; reflexivity.
  - apply cocycle_sieve_triangle_value.
Defined.

(** Triangle coverage alone reflects simplex equality. *)

(** 仅三角形覆盖就能反映单形相等。 *)

Lemma cocycle_sieve_reflects
    (x y : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
    (H : x↾Sv[Z²(M); R] ≈N y↾Sv[Z²(M); R])
  : x ≈S y.
Proof.
  refine {|lower := _
          |}. intros a d e f g.
  pose (Q := ⟦⟨f, g⟩Ch⟧Ch).
  pose (E := lower (H 2 {|lower := (Q; T Q)
                        |})).
  etransitivity; [| etransitivity].
  - cbn. apply two_cocycle_triangle_proper; exact tt.
  - exact (E fin_first (fin_first⁺)
      (fin_first⁺⁺) (ordinal_step fin_first)
      (ordinal_step (fin_next fin_first))).
  - cbn. apply two_cocycle_triangle_proper; exact tt.
Defined.

(** Retain the extension and its complete uniqueness property. *)

(** 保留延拓及其完整唯一性。 *)

Definition cocycle_sieve_universal
  : ∃ x : (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n,
      is_unique (R := carrier_equiv ((Z²(M) :
        Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n))
        (λ x, x↾Sv[Z²(M); R] ≈N b) x.
Proof.
  exists CocycleSieveSimplex.
  refine {|this := _
          ; that := _
          |}.
  - exact cocycle_sieve_filler.
  - intros y Hy. apply cocycle_sieve_reflects.
    transitivity b; [exact Hy | symmetry; apply cocycle_sieve_filler].
Defined.

End SieveValues.
