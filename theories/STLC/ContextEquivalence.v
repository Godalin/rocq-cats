From Cats Require Export STLC.TypeCategory.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Cat.Induced.

(** * Equivalence of Context and Type Presentations

    Singleton contexts give a fully faithful inclusion. Packing gives its
    explicit quasi-inverse; the comparison maps are the existing context
    packing isomorphisms. *)

(** * 上下文与类型呈现的等价

    单变量上下文给出全忠实嵌入；打包给出显式拟逆，比较映射使用已有的上下文
    打包同构。 *)

(** Include a type as its singleton context, preserving its hom-set verbatim. *)

(** 将类型嵌为其单变量上下文，原样保留 Hom 广集。 *)

Definition SingletonF@{b e l +} (B : Type@{b})
  : Functor (TyCat@{b e l} B) (CtxCat@{b e l} B)
  := @InducedInclusionF (CtxCat@{b e l} B) (Ty B)
      (λ A, ctx_snoc ctx_empty A).

(** Pack a context into its product type, transporting each substitution
    along the existing packing and unpacking maps. *)

(** 将上下文打包为积类型，沿已有打包、拆包映射运输每条替换。 *)

Definition PackF@{b e l +} (B : Type@{b})
  : Functor (CtxCat@{b e l} B) (TyCat@{b e l} B)
  := @InducedRepresentativesF (CtxCat@{b e l} B) (Ty B)
      (λ A, ctx_snoc ctx_empty A) (@CtxTy B)
      (λ Γ, iso_symm (ctx_pack_iso Γ)).

(** Unpacking is the natural counit from singleton packing to the context. *)

(** 拆包是从单变量打包上下文到原上下文的自然余单位。 *)

Definition singleton_pack_nat_iso@{b e l +} (B : Type@{b})
  : (SingletonF B ∘F PackF B) ≅N (@IdF (CtxCat@{b e l} B))
  := @induced_counit_nat_iso (CtxCat@{b e l} B) (Ty B)
      (λ A, ctx_snoc ctx_empty A) (@CtxTy B)
      (λ Γ, iso_symm (ctx_pack_iso Γ)).

(** The other composite is naturally isomorphic to the type identity. *)

(** 另一复合自然同构于类型范畴的恒等。 *)

Definition pack_singleton_nat_iso@{b e l +} (B : Type@{b})
  : (PackF B ∘F SingletonF B) ≅N (@IdF (TyCat@{b e l} B))
  := @induced_unit_nat_iso (CtxCat@{b e l} B) (Ty B)
      (λ A, ctx_snoc ctx_empty A) (@CtxTy B)
      (λ Γ, iso_symm (ctx_pack_iso Γ)).

(** The two syntactic categories are equivalent in the library's category
    of categories, whose specified equality is natural isomorphism. *)

(** 两种语法范畴在本库的范畴之范畴中等价，其中指定相等为自然同构。 *)

Definition ContextCategoryEquivalence@{b e l +} (B : Type@{b})
  : (TyCat@{b e l} B) ≅[CatCat] (CtxCat@{b e l} B).
Proof.
  exists (CatCatHom (SingletonF B)), (CatCatHom (PackF B)). split.
  - pose (N := pack_singleton_nat_iso@{b e l _ _ _} B).
    unshelve refine (existT _ {|nt := _
                              ; nt_naturality := _
                              |} _).
    + exact (λ X, N.1 X).
    + intros X Y f. exact (nt_naturality N.1 f).
    + intros X. exact (N.2 X).
  - pose (N := singleton_pack_nat_iso@{b e l _ _ _} B).
    unshelve refine (existT _ {|nt := _
                              ; nt_naturality := _
                              |} _).
    + exact (λ X, N.1 X).
    + intros X Y f. exact (nt_naturality N.1 f).
    + intros X. exact (N.2 X).
Defined.
