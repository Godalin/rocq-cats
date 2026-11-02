From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Equalizer.
From Cats Require Export
  Cat.Limit.Construction
  Cat.Diagram.Free.

(** * Limits Specified by Graph Generators

    Products are indexed by vertices and generators, not by all paths. *)

(** * 由图生成元指定的极限

    积仅由顶点和生成边索引，不由所有路径索引。 *)

Definition GraphTargets {G : Graph} {C : Cat} (D : Functor (FreeCat G) C)
    (a : GraphEdges G)
  : @Ob C
  := D a.2.1.

Section GraphLimits.
Context {G : Graph} {C : Cat} (D : Functor (FreeCat G) C).
Context `{HO : !HasLimit C (DiscreteF (DiagramObjects D))}.
Context `{HG : !HasLimit C (DiscreteF (GraphTargets D))}.

(** The source constraint applies each generating arrow to its source
    projection. *)

(** 源约束将每条生成箭头作用于其源投影。 *)

Definition graph_product_source
  : Hom Π[DiagramObjects D] Π[GraphTargets D]
  := Π⟨λ a, fmap D (ιG a.2.2) ∘ πΠ[DiagramObjects D] a.1⟩.

(** The target constraint selects the target projection of each generating
    edge. *)

(** 目标约束选取每条生成边的目标投影。 *)

Definition graph_product_target
  : Hom Π[DiagramObjects D] Π[GraphTargets D]
  := Π⟨λ a, πΠ[DiagramObjects D] a.2.1⟩.

(** Equalizing generator constraints gives commutativity on each edge. *)

(** 等化生成边约束，得到每条边上的交换性。 *)

Lemma graph_product_comm {E : @Ob C} (e : Hom E Π[DiagramObjects D])
    (H : graph_product_source ∘ e ≈ graph_product_target ∘ e)
    {x y : @Vertex G} (f : Edge x y)
  : fmap D (ιG f) ∘ (πΠ[DiagramObjects D] x ∘ e) ≈ πΠ[DiagramObjects D] y ∘ e.
Proof.
  pose (a := ((x; (y; f)) : GraphEdges G)).
  transitivity ((πΠ[GraphTargets D] a ∘ graph_product_source) ∘ e).
  - unfold graph_product_source. rewrite indexed_product_β, comp_assoc. reflexivity.
  - rewrite comp_assoc, H, <- comp_assoc.
    unfold graph_product_target. rewrite indexed_product_β. reflexivity.
Qed.

(** Extend equalizer legs on vertices to all free paths. *)

(** 将顶点上的等化子锥腿延拓到所有自由路径。 *)

Definition GraphEqualizerCone {E : @Ob C} (e : Hom E Π[DiagramObjects D])
    (H : graph_product_source ∘ e ≈ graph_product_target ∘ e)
  : E ⇒Δ D
  := @FreeCone G C D E (λ x, πΠ[DiagramObjects D] x ∘ e)
    (λ x y f, graph_product_comm e H f).

(** The generator-constraint equalizer gives the limit of the free diagram. *)

(** 生成边约束的等化子给出自由图式的极限。 *)

Definition graph_products_equalizer_limit {E : @Ob C}
    {e : Hom E Π[DiagramObjects D]}
    (H : graph_product_source ∘ e ≈ graph_product_target ∘ e)
    (HE : is_equalizer graph_product_source graph_product_target E e)
  : is_limit (GraphEqualizerCone e H).
Proof.
  refine (product_cone_equalizer_limit D (GraphEqualizerCone e H) _ _ HE).
  - intros x. reflexivity.
  - intros X μ. apply indexed_product_hom_ext. intros [x [y f]].
    unfold graph_product_source, graph_product_target.
    rewrite <- !comp_assoc, !indexed_product_β, comp_assoc, !indexed_product_β.
    transitivity (μ y).
    + exact (free_cone_edge μ f).
    + symmetry. apply (indexed_product_β (D := DiagramObjects D)).
Defined.

(** Choose one free-diagram limit using vertex and generator products. *)

(** 用顶点积与生成边积选择一个自由图式的极限。 *)

Program Definition GraphProductsEqualizerLimit `{HE : !HasEqualizer C}
  : HasLimit C D
  :=
  {|Lim := Eq[graph_product_source, graph_product_target]
  ; limit_cone := GraphEqualizerCone
      ιeq[graph_product_source, graph_product_target] equalizer_comm
  |}.
Next Obligation. apply graph_products_equalizer_limit. exact equalizer_universal. Defined.

End GraphLimits.

(** Choose all free-shape limits from vertex products, generator products and
    equalizers. *)

(** 由顶点积、生成边积及等化子选择自由形状的全部极限。 *)

Program Definition GraphProductsEqualizerLimits {G : Graph} {C : Cat}
    `{HO : !HasLimitsOfShape C (DiscreteCat (@Vertex G))}
    `{HG : !HasLimitsOfShape C (DiscreteCat (GraphEdges G))}
    `{HE : !HasEqualizer C}
  : HasLimitsOfShape C (FreeCat G)
  :=
  {|hasLimit D := GraphProductsEqualizerLimit D
  |}.
