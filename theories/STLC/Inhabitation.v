From Cats Require Export STLC.Comparison.
From Cats Require Import
  Cat.Core
  Cat.CCC
  Cat.Functor.Closed.

(** * Inhabitation Soundness and Completeness

    Validity carries a chosen morphism in every CCC model at the common
    bound [Cat@{b b e l l}]. The reverse direction reuses the syntactic CCC
    and the canonical comparison isomorphisms. All witnesses remain in [Type]. *)

(** * 可居留性的可靠性与完备性

    有效性在共同大小界 [Cat@{b b e l l}] 内为每个 CCC 模型携带选定态射。
    反方向复用语法 CCC 与规范比较同构，所有见证均保留在 [Type] 中。 *)

(** ** The data returned by the two directions

    This entry asks for a term in a context, not an equation of two terms
    already supplied. Soundness maps a term to its interpretation in each
    model. The input to completeness is a function of the model, its
    chosen CCC structure and its base assignment, returning an actual
    morphism. No coherence between different models is demanded of this
    family, and no equality on such families is added.

    Apply the family to [TyCat B]. The type comparison postcomposes its
    morphism and the inverse context comparison precomposes it, obtaining
    a literal arrow [CtxTy Γ → A]. Its singleton-context substitution has
    a newest component, a term with one packed-context variable. Substituting
    [ctx_pack_sub Γ] changes that source back to [Γ]. This extraction
    explains both the constructivity of completeness and why a Prop-only
    nonemptiness premise would be a different interface.

    The displayed Type-valued equivalence bundles two maps. It supplies
    neither equality of types nor inverse laws on witnesses. It concerns
    existence of an intrinsically typed term, not typing a given untyped
    expression and not deciding whether such a term exists. *)

(** ** 两个方向返回什么数据

    此入口要求上下文中的一个项，不是两个已给定项之间的等式。可靠性把项送到
    各模型中的解释。完备性的输入是一个函数：接受模型、选定 CCC 结构与基类型
    赋值，返回实际态射。不要求这个族在不同模型之间满足额外相干性，也不为
    这些族另加相等。

    将该族用于 [TyCat B]。在所得态射之后复合类型比较，在其之前复合上下文
    比较的逆，得到字面箭头 [CtxTy Γ → A]。其单变量上下文替换的最新分量
    就是只有一个打包上下文变量的项。再代入 [ctx_pack_sub Γ]，将源改回 [Γ]。
    这既解释了完备性的构造性，也说明仅有 Prop 层非空性前提会是另一种接口。

    所陈述的 Type 值等价打包两个映射，不提供类型相等或见证上的互逆律。
    它涉及内在带类型项的存在，不为给定无类型表达式赋型，也不判定这样的项
    是否存在。 *)

Local Open Scope cat_scope.

Section CanonicalInhabitation.
Universes b e l.
Context {B : Type@{b}}.
Let C
  : Cat
  := TyCat@{b e l} B.
Local Instance canonical_ccc
  : CCC C
  := TyCat_CCC B.
Local Instance canonical_identity
  : IsCCCF (@IdF C) canonical_ccc canonical_ccc
  := IdF_IsCCCF C canonical_ccc.
Let β (b : B)
  : ty_base b ≅[C] ty_base b
  := iso_refl.

(** A morphism in the recursive syntactic model supplies a term. The
    comparison isomorphisms turn it into a singleton-context substitution;
    its newest component is then substituted back into the original context. *)

(** 递归语法模型中的态射给出一个项。比较同构将它转为单变量上下文替换，
    再将最新分量代回原上下文。 *)

Definition tm_interp_canonical_inhabited {Γ : Ctx B} {A : Ty B}
    (f : Hom (CtxI (HC := canonical_ccc) (@ty_base B) Γ)
      (TyI (HC := canonical_ccc) (@ty_base B) A))
  : Tm Γ A.
Proof.
  pose (z := @context_compare B C canonical_ccc (@IdF C)
    canonical_identity (@ty_base B) β Γ).
  pose (a := @type_compare B C canonical_ccc (@IdF C)
    canonical_identity (@ty_base B) β A).
  pose (σ := a.1 ∘ f ∘ z.2.1).
  exact (subst (σ A var_zero) (ctx_pack_sub Γ)).
Defined.

End CanonicalInhabitation.

(** A uniform family of semantic morphisms at the common universe bound. *)

(** 共同宇宙界内统一给出的语义态射族。 *)

Definition TmModelInhabited@{b e l +} {B : Type@{b}}
    (Γ : Ctx B) (A : Ty B)
  : Type
  := ∀ (C : Cat@{b b e l l}) (HC : CCC C) (I : B → @Ob C),
      (@Hom C) (@CtxI B C HC I Γ) (@TyI B C HC I A).

(** Interpret an intrinsically typed term in each chosen CCC model. *)

(** 在每个选定 CCC 模型中解释一个内在带类型的项。 *)

Definition tm_inhabitation_soundness@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : TmModelInhabited@{b e l _ _ _ _} Γ A
  := λ C HC I, @tm_interp B C HC I Γ A t.

(** Instantiate the model family with the syntactic CCC and recover a term
    using the canonical comparison maps. No normalization or choice is needed. *)

(** 将模型族实例化为语法 CCC，再由规范比较映射恢复一个项；
    无须正规化或选择原理。 *)

Definition tm_inhabitation_completeness@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B}
    (H : TmModelInhabited@{b e l _ _ _ _} Γ A)
  : Tm Γ A
  := tm_interp_canonical_inhabited
      (H (TyCat@{b e l} B) (TyCat_CCC B) (@ty_base B)).

(** This Type-valued equivalence bundles the two constructive maps; it makes
    no claim that terms or families of semantic witnesses are equal. Under
    Curry--Howard--Lambek it expresses provability completeness for unit,
    conjunction and implication, separately from beta/eta equality. *)

(** 此 Type 值等价打包两个构造性映射，不断言项或语义见证族相等。
    在 Curry--Howard--Lambek 对应下，它表达单位、合取与蕴含片段的可证性
    完备性，与 βη 等式完备性分开陈述。 *)

Definition tm_inhabitation_soundness_iff_completeness@{b e l +}
    {B : Type@{b}} (Γ : Ctx B) (A : Ty B)
  : Tm Γ A ↔ TmModelInhabited@{b e l _ _ _ _} Γ A
  := (tm_inhabitation_soundness, tm_inhabitation_completeness).
