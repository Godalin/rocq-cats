From Cats Require Export
  Cat.Diagram.Prism
  Cat.Functor.Product.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Uncurry
  Cat.Natural.

(** * Reading a Natural Transformation from a Prism

    A functor on a product with the ordinal interval contains two boundary
    functors and arrows between them. Fix arbitrary categories [C], [D].
    Product restriction extracts those boundaries and their transformation.
    Rebuilding the prism recovers the original functor by a natural
    isomorphism with identity components, not equality of functor records. *)

(** * 从棱柱读出自然变换

    与序数区间的积上的函子包含两个边界函子及其间的箭头。固定任意范畴
    [C]、[D]，使用积限制提取这些边界及其自然变换。重建棱柱通过分量为恒等的
    自然同构恢复原函子，不比较函子记录的原生相等。 *)

(** The bottom and top edges are the boundary functors on [f]. The vertical
    edges are the extracted transformation; %$\delta:0\to1$% denotes the
    time step. This square commutes because
    [(f, id) ∘ (id, step)] and [(id, step) ∘ (f, id)] are equal in the product
    category. The reusable construction is
    %\coqref{Cats.Cat.Functor.Product.ProductAtN}{%[ProductAtN]%}%. *)

(** 下边和上边是边界函子在 [f] 上的作用，竖边是提取的自然变换。积范畴中
    [(f, id) ∘ (id, step)] 与 [(id, step) ∘ (f, id)] 相等，所以方形交换；
    图中 %$\delta:0\to1$% 表示时间步。
    此处复用的构造是
    %\coqref{Cats.Cat.Functor.Product.ProductAtN}{%[ProductAtN]%}%。 *)

(** @lang both
    %\[
    \begin{tikzcd}[column sep=large,row sep=large]
      K(x,0) \arrow[r,"{K(f,\mathrm{id}_0)}"]
        \arrow[d,"{K(\mathrm{id}_x,\delta)}"'] &
      K(y,0) \arrow[d,"{K(\mathrm{id}_y,\delta)}"] \\
      K(x,1) \arrow[r,"{K(f,\mathrm{id}_1)}"'] & K(y,1)
    \end{tikzcd}
    \]% *)

Section PrismReconstruction.
Context {C D : Cat} (K : Functor (C ×C [Ord 1]) D).

(** Read the time edge at each object. Naturality is the general product
    restriction law, so no groupoid or invertible-component assumption enters. *)

(** 在每个对象处读出时间边。自然性来自一般积限制律，因此无需群胚或分量
    可逆的假设。 *)

Definition PrismTransformationN
  : π1F K fin_first ⇒ π1F K (fin_next fin_first)
  := ProductAtN K (ordinal_step fin_first).

(** Each prism arrow is recovered by the parameter-first factorization of
    its product arrow. The concrete interval has only the cases 00, 01, 11. *)

(** 按积箭头先参数后第一坐标的分解，恢复棱柱的每条箭头。具体区间只有
    00、01、11 三种情形。 *)

Program Definition PrismReconstructionN
  : NaturalPrismF PrismTransformationN ⇒ K
  :=
  {|nt p := _
  |}.
Next Obligation.
  destruct p as [x [[] | [[] | []]]]; exact id.
Defined.
Next Obligation.
  destruct X as [x [[] | [[] | []]]], Y as [y [[] | [[] | []]]],
    f as [f a]; cbn in *; try solve [destruct a].
  - rewrite !comp_id_l, !comp_id_r.
    apply functor_fmap_proper. split; [reflexivity | exact tt].
  - rewrite comp_id_l, comp_id_r.
    destruct a. symmetry.
    exact (product_at_map K (b := fin_first)
      (b' := fin_next fin_first) f (ordinal_step fin_first)).
  - rewrite !comp_id_l, !comp_id_r.
    apply functor_fmap_proper. split; [reflexivity | exact tt].
Defined.

(** The comparison components are identities at the two concrete time
    positions, and hence are invertible without any assumption on [K]. *)

(** 比较分量在两个具体时间位置处都是恒等，故无需对 [K] 作假设便可逆。 *)

Definition prism_reconstruction_iso
  : NaturalPrismF PrismTransformationN ≅N K.
Proof.
  exists PrismReconstructionN. intros [x [[] | [[] | []]]];
    exists id; split; apply comp_id_l.
Defined.

End PrismReconstruction.

(** ** Boundary Comparisons for a Constructed Prism

    Fix functors [F], [G] from [C] to [D] and a transformation [α].
    Its constructed prism restricts to [F] or [G] by canonical identity
    comparisons. These comparisons align the endpoints of the round trip. *)

(** ** 所构造棱柱的边界比较

    固定从 [C] 到 [D] 的函子 [F]、[G] 及自然变换 [α]。它所构造的棱柱
    通过规范恒等比较限制为 [F] 或 [G]；这些比较对齐往返律的端点。 *)

Section PrismBoundaries.
Context {C D : Cat} {F G : Functor C D} (α : F ⇒ G).

(** Restriction to either time position compares with the corresponding
    boundary functor; the component remains a transparent identity. *)

(** 在任一时间位置的限制与对应边界函子比较，分量保留为透明恒等。 *)

Program Definition NaturalPrismBoundaryN (i : Ordinal 1)
  : π1F (NaturalPrismF α) i ⇒
      (if ordinal_interval_side i then G else F)
  :=
  {|nt x := _
  |}.
Next Obligation.
  destruct i as [[] | [[] | []]]; exact id.
Defined.
Next Obligation.
  destruct i as [[] | [[] | []]]; cbn;
    rewrite !comp_id_l, !comp_id_r; reflexivity.
Defined.

(** The boundary comparison is a natural isomorphism with explicit inverses. *)

(** 边界比较是带显式逆的自然同构。 *)

Definition natural_prism_boundary_iso (i : Ordinal 1)
  : π1F (NaturalPrismF α) i ≅N
      (if ordinal_interval_side i then G else F).
Proof.
  exists (NaturalPrismBoundaryN i). intros x.
  destruct i as [[] | [[] | []]]; exists id; split; apply comp_id_l.
Defined.

(** Reading a constructed prism recovers the original transformation after
    the canonical boundary comparisons. No endpoint record is identified. *)

(** 经过规范边界比较，读出所构造的棱柱可恢复原自然变换，不识别端点记录。 *)

Lemma natural_prism_transformation_β
  : (NaturalPrismBoundaryN (fin_next fin_first) ∘Nv
      PrismTransformationN (NaturalPrismF α)) ≈N
      (α ∘Nv NaturalPrismBoundaryN fin_first).
Proof.
  intros x. cbn. rewrite !comp_id_l, !comp_id_r, functor_id.
  apply comp_id_l.
Defined.

End PrismBoundaries.

(** ** Comparing Prisms by Their Boundaries

    Fix transformations [α] and [β] between possibly different boundary
    functors. A commuting square between them gives a comparison of prisms.
    Reuse [ArrowN] in the functor category and uncurrying; no new prism
    naturality proof or invertibility assumption is required. *)

(** ** 通过边界比较棱柱

    固定端点函子可能不同的自然变换 [α]、[β]。它们之间的交换方形给出棱柱
    的比较。在函子范畴中复用 [ArrowN] 并去柯里化，无需重证棱柱的自然性，
    也无需可逆假设。 *)

Section PrismComparisons.
Context {C D : Cat} {F G F' G' : Functor C D}
    (α : F ⇒ G) (β : F' ⇒ G')
    (a : F ⇒ F') (b : G ⇒ G')
    (H : (b ∘Nv α) ≈N (β ∘Nv a)).

(** Here the four vertices are functors and each edge is a natural
    transformation. The hypothesis [H] is the commutativity of this square.
    Its extension reuses
    %\coqref{Cats.Cat.Diagram.Arrow.ArrowN}{%[ArrowN]%}% and
    %\coqref{Cats.Cat.Functor.Uncurry.UncurryN}{%[UncurryN]%}%. *)

(** 此处四个顶点是函子，每条边是自然变换；假设 [H] 就是这个方形的交换性。
    其延拓复用
    %\coqref{Cats.Cat.Diagram.Arrow.ArrowN}{%[ArrowN]%}% 和
    %\coqref{Cats.Cat.Functor.Uncurry.UncurryN}{%[UncurryN]%}%。 *)

(** @lang both
    %\[
    \begin{tikzcd}
      F \arrow[r,"\alpha"] \arrow[d,"a"'] & G \arrow[d,"b"] \\
      F' \arrow[r,"\beta"'] & G'
    \end{tikzcd}
    \]% *)

(** Extend the commuting boundary square along the walking arrow. *)

(** 沿步行箭头延拓交换的边界方形。 *)

Definition NaturalPrismN
  : NaturalPrismF α ⇒ NaturalPrismF β
  := (@ArrowN (Fct C D) (@ArrowDiagram (Fct C D) F G α)
      (@ArrowDiagram (Fct C D) F' G' β) a b H)^uncN
      ∘Nr PairF (OrdinalArrowF ∘F SndF C [Ord 1]) (FstF C [Ord 1]).

(** The extension has precisely the prescribed initial boundary. *)

(** 延拓具有所指定的初始边界。 *)

Lemma natural_prism_β0 (x : @Ob C)
  : NaturalPrismN (x, fin_first) ≈ a x.
Proof. reflexivity. Defined.

(** The extension has precisely the prescribed final boundary. *)

(** 延拓具有所指定的终止边界。 *)

Lemma natural_prism_β1 (x : @Ob C)
  : NaturalPrismN (x, fin_next fin_first) ≈ b x.
Proof. reflexivity. Defined.

(** Invertible boundary comparisons give an invertible prism comparison,
    even when the two time transformations themselves are not invertible. *)

(** 可逆的边界比较给出可逆的棱柱比较，即使两个时间自然变换本身不可逆。 *)

Definition natural_prism_NatIso
    (Ha : a ⦂ F ≅N F') (Hb : b ⦂ G ≅N G')
  : NaturalPrismN ⦂ NaturalPrismF α ≅N NaturalPrismF β.
Proof.
  intros [x [[] | [[] | []]]]; [exact (Ha x) | exact (Hb x)].
Defined.

End PrismComparisons.

(** Equal boundary maps give equal prism comparisons, independently of the
    witnesses proving that the boundary squares commute. *)

(** 相等的边界映射给出相等的棱柱比较，不依赖边界方形交换性的证明见证。 *)

Lemma natural_prism_eq {C D : Cat} {F G F' G' : Functor C D}
    (α : F ⇒ G) (β : F' ⇒ G') (a a' : F ⇒ F') (b b' : G ⇒ G')
    (H : (b ∘Nv α) ≈N (β ∘Nv a))
    (H' : (b' ∘Nv α) ≈N (β ∘Nv a'))
    (Ha : a ≈N a') (Hb : b ≈N b')
  : NaturalPrismN α β a b H ≈N NaturalPrismN α β a' b' H'.
Proof.
  intros [x [[] | [[] | []]]]; [exact (Ha x) | exact (Hb x)].
Defined.

(** ** Reconstruction with Prescribed Boundary Comparisons

    Fix an arbitrary prism [K], a transformation [α], and maps [a], [b]
    from its endpoints to the restrictions of [K]. Their commuting square
    extends uniquely to a natural comparison with [K]. Uniqueness means
    pointwise hom equality; it does not compare proof fields. *)

(** ** 指定边界比较的重建

    固定任意棱柱 [K]、自然变换 [α] 及从其端点到 [K] 的限制的映射 [a]、[b]。
    它们的交换方形唯一延拓为到 [K] 的自然比较。唯一性采用逐点 Hom 相等，
    不比较证明字段。 *)

Section PrescribedPrism.
Context {C D : Cat} (K : Functor (C ×C [Ord 1]) D)
    {F G : Functor C D} (α : F ⇒ G)
    (a : F ⇒ π1F K fin_first)
    (b : G ⇒ π1F K (fin_next fin_first))
    (H : (b ∘Nv α) ≈N (PrismTransformationN K ∘Nv a)).

(** Compose extension of the boundary square with prism reconstruction. *)

(** 将边界方形的延拓与棱柱重建复合。 *)

Definition PrismComparisonN
  : NaturalPrismF α ⇒ K
  := PrismReconstructionN K ∘Nv
      NaturalPrismN α (PrismTransformationN K) a b H.

(** The candidate property records both prescribed boundary components. *)

(** 候选性质记录两个指定的边界分量。 *)

Definition is_prism_comparison (κ : NaturalPrismF α ⇒ K)
  : Type
  := (∀ x, κ (x, fin_first) ≈ a x) ∧
      (∀ x, κ (x, fin_next fin_first) ≈ b x).

(** Every object lies at one of the two time positions, so the boundary
    data determine the whole natural comparison uniquely. *)

(** 每个对象都处于两个时间位置之一，因此边界数据唯一确定整个自然比较。 *)

Definition prism_comparison_universal
  : is_unique (R := @NatEq _ _ _ _) is_prism_comparison PrismComparisonN.
Proof.
  refine {|this := _
          ; that := _
          |}.
  - split; intros x; cbn; apply comp_id_l.
  - intros κ [H0 H1] [x [[] | [[] | []]]]; cbn;
      rewrite comp_id_l; [exact (H0 x) | exact (H1 x)].
Defined.

(** If the prescribed boundaries are natural isomorphisms, so is the
    unique comparison. Its inverse components remain computational witnesses. *)

(** 若指定的边界是自然同构，则唯一比较也是自然同构，逆分量保留为计算见证。 *)

Definition prism_comparison_NatIso
    (Ha : a ⦂ F ≅N π1F K fin_first)
    (Hb : b ⦂ G ≅N π1F K (fin_next fin_first))
  : PrismComparisonN ⦂ NaturalPrismF α ≅N K.
Proof.
  apply nt_comp_v_NatIso.
  - exact (prism_reconstruction_iso K).2.
  - exact (natural_prism_NatIso α (PrismTransformationN K) a b H Ha Hb).
Defined.

End PrescribedPrism.
