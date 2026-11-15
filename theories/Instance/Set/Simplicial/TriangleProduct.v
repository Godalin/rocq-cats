From Cats Require Export
  Cat.Shape.Simplex.TriangleProductIntersection
  Instance.Set.Simplicial.Homotopy.Triangle.
From Cats Require Import
  Instance.Set.PresheafDescent
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Triangle Products are Covered by Six Simplices

    The two shape coordinates give generators of the actual parameter
    presheaf [Δ[2] × Δ[2]], with independent carrier/equality bounds.
    The computed factorization is a cover in the sense of
    %\coqref{Cats.Instance.Set.PresheafDescent.is_presheaf_cover}
    {%[is_presheaf_cover]%}%. Consequently a given map out of this
    product is determined by six four-simplex values.

    Determination is not extension from a subdomain: the horn attachment
    geometry and the supplied values' compatibility are separate tasks.
    The concrete nine-step geometry is developed in
    %\coqref{Cats.Instance.Set.Simplicial.TriangleHorn.triangle_horn_stage_preimage_iff}
    {%[triangle_horn_stage_preimage_iff]%}%, before its future pushout consumer. *)

(** * 六个单形覆盖实际三角积

    两个形状坐标给出实际参数预层 [Δ[2] × Δ[2]] 的生成元，载体／相等界
    独立。计算分解是 %\coqref{Cats.Instance.Set.PresheafDescent.is_presheaf_cover}
    {%[is_presheaf_cover]%}% 意义下的覆盖，因此从该积出发的给定映射由六个
    四单形值确定。

    确定性不等于从子域延拓；horn 附着几何及给定值的相容性仍是独立任务。
    具体九步几何见
    %\coqref{Cats.Instance.Set.Simplicial.TriangleHorn.triangle_horn_stage_preimage_iff}
    {%[triangle_horn_stage_preimage_iff]%}%，其预层推出消费者留待后续。 *)

(** The generator retains both actual monotone coordinates. *)

(** 生成元保留两个实际保序坐标。 *)

Definition simplex_triangle_product_generator@{u p +} (i : Ordinal 5)
  : SimplicialParameterF
      (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2 4
  := ({|lower := SimplexTriangleProductSpaceF i|},
      {|lower := SimplexTriangleProductTimeF i|}).

(** Cover every source degree, including repeated vertices, by the
    existing transparent two-pivot factorization. *)

(** 通过已有透明双枢轴分解覆盖全部来源维数，包括重复顶点。 *)

Definition simplex_triangle_product_cover@{u p +}
  : is_presheaf_cover
      (Q := SimplicialParameterF
        (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2)
      simplex_triangle_product_generator.
Proof.
  intros n [[a] [b]].
  destruct (SimplexTriangleProductFactor a b) as [i [h [E F]]].
  exists i, h. split; refine {|lower := _|}; [exact E | exact F].
Defined.

(** ** Reading Given Product Maps

    Fix any target simplicial setoid at independent carrier/equality
    sizes. No Kan selection, algebra structure or equality of naturality
    records is needed. All equations use the target's specified equality. *)

(** ** 读取给定积映射

    固定载体／相等大小独立的任意目标单纯广集，不要求 Kan 选择、代数结构或
    自然性记录相等；方程使用目标的指定相等。 *)

Section ProductMaps.
Universes u p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.

Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialParameterF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2.

(** Evaluate at an actual maximal staircase. *)

(** 在实际最大阶梯处求值。 *)

Definition simplex_triangle_product_eval (K : Q ⇒ X) (i : Ordinal 5)
  : X 4
  := K 4 (simplex_triangle_product_generator i).

(** Naturality reads an arbitrary simplex through the computed factor.
    The statement retains the very same factorization witness. *)

(** 自然性通过计算因子读取任意单形；陈述保留同一个分解见证。 *)

Lemma simplex_triangle_product_eval_factor (K : Q ⇒ X) {n : nat}
    (a b : (@Hom Δ) n 2)
  : K n ({|lower := a|}, {|lower := b|}) ≈S
      X[(SimplexTriangleProductFactor a b).2.1]Δ
        (simplex_triangle_product_eval K
          (SimplexTriangleProductFactor a b).1).
Proof.
  pose (P := SimplexTriangleProductFactor a b).
  transitivity (K n
    ({|lower := SimplexTriangleProductSpaceF P.1 ∘ P.2.1|},
     {|lower := SimplexTriangleProductTimeF P.1 ∘ P.2.1|})).
  - apply func_proper. split; refine {|lower := _|}; symmetry;
      [exact (fst P.2.2) | exact (snd P.2.2)].
  - exact (simplex_restrict_natural K P.2.1
      (simplex_triangle_product_generator P.1)).
Defined.

(** Six values determine specified natural equality of given maps;
    this does not identify maps that choose different new cell values. *)

(** 六个值确定给定映射的指定自然相等，不将新单形取值不同的映射等同。 *)

Lemma simplex_triangle_product_map_eq_iff (K L : Q ⇒ X)
  : (K ≈N L) ↔ ∀ i,
      simplex_triangle_product_eval K i ≈S simplex_triangle_product_eval L i.
Proof.
  split.
  - intros E i. exact (E 4 (simplex_triangle_product_generator i)).
  - intros E n [[a] [b]].
    transitivity (X[(SimplexTriangleProductFactor a b).2.1]Δ
      (simplex_triangle_product_eval K (SimplexTriangleProductFactor a b).1)).
    + apply simplex_triangle_product_eval_factor.
    + transitivity (X[(SimplexTriangleProductFactor a b).2.1]Δ
        (simplex_triangle_product_eval L (SimplexTriangleProductFactor a b).1)).
      * apply func_proper. apply E.
      * symmetry. apply simplex_triangle_product_eval_factor.
Defined.

End ProductMaps.
