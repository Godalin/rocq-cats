From Cats Require Export STLC.Comparison.
From Cats Require Import
  Cat.Core
  Cat.CCC
  Cat.Functor.Closed.

(** * The Canonical Syntactic Model

    Recursive interpretation in the syntactic CCC reflects beta/eta equality
    and recovers terms from semantic morphisms. The existing comparison
    isomorphisms supply the common foundation for equational and inhabitation
    completeness at a universe bound containing the syntactic model. *)

(** * 规范语法模型

    语法 CCC 中的递归解释反映 βη 相等，并能从语义态射恢复项。
    已有的比较同构为等式与可居留性完备性提供共同基础；
    所用宇宙界包含该语法模型。 *)

Local Open Scope cat_scope.
Local Open Scope stlc_sub_scope.

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
    beta/eta equality. Context and type comparison maps are isomorphisms. *)

(** 递归语法解释中的相等恰好反映 βη 相等；上下文与类型比较均为同构。 *)

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
  assert (Hq : SubTmEq@{b e _} (quote_tm t ∘Sub z.1)
    (quote_tm u ∘Sub z.1)).
  { transitivity (sub_comp
      (@type_compare B C canonical_ccc (@IdF C)
        canonical_identity (@ty_base B) β A).1
      (tm_interp (C := C) (HC := canonical_ccc) (@ty_base B) t)).
    - symmetry. exact Ht.
    - rewrite H. exact Hu. }
  assert (Hz : SubTmEq@{b e _} (z.1 ∘Sub z.2.1) sub_id).
  { exact (snd z.2.2). }
  apply quote_tm_faithful.
  transitivity ((quote_tm t ∘Sub z.1) ∘Sub z.2.1).
  - symmetry. rewrite sub_comp_tm_assoc, Hz, sub_comp_tm_id_r. reflexivity.
  - rewrite Hq, sub_comp_tm_assoc, Hz, sub_comp_tm_id_r. reflexivity.
Qed.

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

End CanonicalModel.
