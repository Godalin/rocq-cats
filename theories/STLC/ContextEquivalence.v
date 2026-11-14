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

(** ** Comparing presentations by functors

    [SingletonF] includes a type as its one-variable context. Its homs are
    those already used by [TyCat], so the inclusion keeps the specified
    arrow equality. Conversely, [PackF] sends a context to [CtxTy Γ] and
    transports a context arrow using the packing and unpacking maps.

    Their composites need not be equal to the identity functors. The
    context packing isomorphisms supply the relevant natural comparisons,
    yielding [ContextCategoryEquivalence]. This is the representation
    independence needed to use whichever presentation suits a proof.
    Inverse arrows and their laws are supplied explicitly; neither equality
    of object lists nor equality of functor-law proofs is required. *)

(** ** 用函子比较呈现

    [SingletonF] 把类型嵌为其单变量上下文，Hom 就是 [TyCat] 已有的 Hom，
    因而嵌入保留指定箭头相等。反向的 [PackF] 把上下文送到 [CtxTy Γ]，
    并使用打包和拆包映射运输上下文箭头。

    两个复合无须等于恒等函子；上下文打包同构给出所需的自然比较，形成
    [ContextCategoryEquivalence]。这使证明可以选用更合适的呈现，而不依赖
    表示细节。逆箭头及其定律都显式给出，不要求对象列表相等，也不要求函子
    定律证明相等。 *)

(** Include a type as its singleton context, preserving its hom-set verbatim. *)

(** 将类型嵌为其单变量上下文，原样保留 Hom 广集。 *)

Definition SingletonF@{b e l +} (B : Type@{b})
  : Fct (TyCat@{b e l} B) (CtxCat@{b e l} B)
  := @InducedInclusionF (CtxCat@{b e l} B) (Ty B)
      (λ A, ctx_snoc ctx_empty A).

(** Pack a context into its product type, transporting each substitution
    along the existing packing and unpacking maps. *)

(** 将上下文打包为积类型，沿已有打包、拆包映射运输每条替换。 *)

Definition PackF@{b e l +} (B : Type@{b})
  : Fct (CtxCat@{b e l} B) (TyCat@{b e l} B)
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
  - pose (N := pack_singleton_nat_iso B).
    unshelve refine (existT _ {|nt := _
                              ; nt_naturality := _
                              |} _).
    + exact (λ X, N.1 X).
    + intros X Y f. exact (nt_naturality N.1 f).
    + intros X. exact (N.2 X).
  - pose (N := singleton_pack_nat_iso B).
    unshelve refine (existT _ {|nt := _
                              ; nt_naturality := _
                              |} _).
    + exact (λ X, N.1 X).
    + intros X Y f. exact (nt_naturality N.1 f).
    + intros X. exact (N.2 X).
Defined.
