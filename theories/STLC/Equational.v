From Cats Require Export STLC.Comparison.
From Cats Require Import
  Cat.Core
  Cat.CCC
  Cat.Functor.Closed.

(** * Equational Soundness and Completeness

    Soundness in [tm_interp_sound] applies to arbitrary model sizes.
    Completeness needs only a common universe bound containing the syntactic
    CCC; this avoids any universe of all categories or resizing principle. *)

(** * 等式可靠性与完备性

    [tm_interp_sound] 中的可靠性适用于任意模型大小。完备性只需要包含语法 CCC
    的共同宇宙界，不构造所有范畴的宇宙，也不使用大小重设原理。 *)

(** ** The question answered by this entry module

    Assume two given terms have the same context and type. Equational
    soundness says their beta/eta equality implies equality of their
    interpretations; its general proof is [tm_interp_sound] in the semantic
    layer, where it is already needed to build interpretation functors.
    This module supplies reflection in the canonical syntactic model and
    bundles the converse with soundness for all models at a common bound.

    The converse specializes model validity to [TyCat B]. Comparison
    isomorphisms relate recursive interpretation to quotation, the context
    comparison is cancelled, and [quote_tm_faithful] returns a beta/eta
    derivation. The bound explicitly contains this model. Merely testing
    equality in one chosen CCC does not provide the all-model premise.
    The conclusion is a derivation in [Type], with no normalization,
    decidable equality or proof-irrelevance requirement. *)

(** ** 这个入口回答什么问题

    设两个给定项具有同样的上下文和类型。等式可靠性说明：βη 相等推出解释
    相等。其一般证明 [tm_interp_sound] 位于语义层，因为构造解释函子时已经
    需要它。本模块提供规范语法模型中的相等反映，并在共同大小界内把全部模型
    的反方向同可靠性一起打包。

    反方向把模型有效性实例化为 [TyCat B]。比较同构把递归解释接到语法还原，
    消去上下文比较后，[quote_tm_faithful] 返回 βη 推导。大小界显式包含该模型。
    只在一个选定 CCC 中检验相等，并不能提供全部模型的前提。结论是 [Type]
    中的推导，不要求正规化、可判定相等或证明无关性。 *)

Local Open Scope cat_scope.
Local Open Scope stlc_sub_scope.

(** ** Reflection in the Canonical Model

    Fix the base-type family [B] and explicitly equip its syntactic category
    with the canonical CCC structure. The identity comparison lets canonical
    interpretation reflect the syntactic equality. *)

(** ** 规范模型中的等式反映

    固定基类型族 [B]，显式为其语法范畴配备规范 CCC 结构，用恒等比较证明规范解释反映语法相等。 *)

Section CanonicalModel.
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

(** Equality in the recursive syntactic interpretation reflects precisely
    beta/eta equality. The proof passes through three representations:

    - [H] compares two recursively interpreted arrows.
    - [context_compare_term] for each term turns this into equality of
      quoted arrows precomposed with the same context comparison [z.1].
    - Precomposition with [z.2.1] cancels that comparison, using its inverse
      law, substitution associativity and the substitution identity law.

    [quote_tm_faithful] then recovers the equation of the original terms.
    Its argument unpacks the quoted arrows by substituting the packed
    identity environment. No step needs a normal form or equality of
    substitution functions. *)

(** 递归语法解释中的相等恰好反映 βη 相等。证明经过三种表示：

    - [H] 比较两条递归解释的箭头。
    - 对两个项分别使用 [context_compare_term]，得到语法还原箭头在同一
      上下文比较 [z.1] 之后的相等。
    - 再预合成 [z.2.1]，借助互逆律、替换结合律及单位律消去比较。

    最后由 [quote_tm_faithful] 恢复原项的等式；其论证代回打包的恒等环境，
    拆开语法还原箭头。全程不需要正规形，也不需要替换函数相等。 *)

Theorem tm_interp_canonical_reflect {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A}
    (H : tm_interp (C := C) (HC := canonical_ccc) (@ty_base B) t ≈
      tm_interp (C := C) (HC := canonical_ccc) (@ty_base B) u)
  : TmEq@{b e _} t u.
Proof.
  pose (z := @context_compare B C canonical_ccc (@IdF C)
    canonical_identity (@ty_base B) β Γ).
  pose proof (@context_compare_term B C canonical_ccc (@IdF C)
    canonical_identity (@ty_base B) β Γ A t) as Ht.
  pose proof (@context_compare_term B C canonical_ccc (@IdF C)
    canonical_identity (@ty_base B) β Γ A u) as Hu.
  assert (Hq : SubTmEq (quote_tm t ∘Sub z.1)
    (quote_tm u ∘Sub z.1)).
  { transitivity (sub_comp
      (@type_compare B C canonical_ccc (@IdF C)
        canonical_identity (@ty_base B) β A).1
      (tm_interp (C := C) (HC := canonical_ccc) (@ty_base B) t)).
    - symmetry. exact Ht.
    - rewrite H. exact Hu. }
  assert (Hz : SubTmEq (z.1 ∘Sub z.2.1) sub_id).
  { exact (snd z.2.2). }
  apply quote_tm_faithful.
  transitivity ((quote_tm t ∘Sub z.1) ∘Sub z.2.1).
  - symmetry. rewrite sub_comp_tm_assoc, Hz, sub_comp_tm_id_r. reflexivity.
  - rewrite Hq, sub_comp_tm_assoc, Hz, sub_comp_tm_id_r. reflexivity.
Qed.

End CanonicalModel.

(** Validity in all CCC models at a common bound. The object/hom bound is b,
    equality witnesses live at e, and category laws at l. Larger or differently
    arranged model universes remain covered separately by soundness. *)

(** 共同大小界内全部 CCC 模型的有效性：对象与 Hom 载体界为 b，相等见证界为 e，
    范畴律界为 l。更大或采用其他大小排列的模型仍由一般可靠性定理覆盖。 *)

Definition TmModelEq@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type
  := ∀ (C : Cat@{b b e l l}) (HC : CCC C) (I : B → @Ob C),
      @HomEq C _ _ (@tm_interp B C HC I Γ A t)
        (@tm_interp B C HC I Γ A u).

Notation "t '≈CCC' u" := (TmModelEq t u)
  (at level 50, no associativity) : stlc_tm_scope.

(** The syntactic model supplies the reverse implication. The forward map
    accepts a beta/eta derivation, then an arbitrary model, its chosen CCC
    structure and a base assignment, returning [tm_interp_sound]. The reverse
    map applies the model family to [TyCat B], [TyCat_CCC B] and [ty_base],
    then uses canonical reflection above. Testing only one other model
    would not justify that specialization.

    The common universe bound must contain this syntactic model. Equality
    witnesses and auxiliary law proofs retain their distinct bounds; there
    is no small type of all categories or resizing assumption. The [↔] is
    [iffT], a pair of maps between Types, without inverse equations on
    derivation witnesses. No normalization, decidability, choice, proof
    irrelevance or extensionality axiom is used. *)

(** 语法模型给出反方向。正向映射接收 βη 推导，再接收任意模型、其选定 CCC
    结构及基类型赋值，返回 [tm_interp_sound]。反向把模型族用于 [TyCat B]、
    [TyCat_CCC B] 和 [ty_base]，再使用上面的规范反映。仅在另一个特定模型中
    检验等式，不能支持这次实例化。

    共同宇宙界必须容纳此语法模型，相等见证与辅助定律证明仍保留不同的界。
    这里没有包含全部范畴的小类型，也没有大小重设假设。[↔] 是 [iffT]，即
    Types 之间的一对映射，不附带推导见证上的互逆方程。证明不使用正规化、
    可判定性、选择、证明无关性或外延公理。 *)

Theorem tm_soundness_iff_completeness@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : TmEq@{b e _} t u ↔ TmModelEq t u.
Proof.
  split.
  - intros H C HC I. exact (@tm_interp_sound B C HC I Γ A t u H).
  - intros H. apply tm_interp_canonical_reflect.
    exact (H (TyCat@{b e l} B) (TyCat_CCC B) (@ty_base B)).
Defined.
